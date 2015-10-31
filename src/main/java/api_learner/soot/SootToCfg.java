/**
 * 
 */
package api_learner.soot;

import java.util.AbstractMap;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import soot.Body;
import soot.Hierarchy;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import api_learner.Options;
import api_learner.soot.SootRunner.CallgraphAlgorithm;
import api_learner.util.Log;

/**
 * This is the main class for the translation. It first invokes Soot to load all
 * classes and perform points-to analysis and then translates them into
 * Boogie/Horn.
 * 
 * @author schaef
 *
 */
public class SootToCfg {

	Map<SootMethod, Set<SootMethod>> callDependencyMap = new HashMap<SootMethod, Set<SootMethod>>();
	Map<SootMethod, LocalCallGraphBuilder> procedureCallGraphs = new HashMap<SootMethod, LocalCallGraphBuilder>();

	/**
	 * Generates the call graph for given input
	 * 
	 * @param input
	 *            either the root folder of a set of class files or a jarfile
	 * @return true if the input could be analyzed and false otherwise.
	 */
	public Collection<String> run(String input) {

		// run soot to load all classes.
		SootRunner runner = new SootRunner();
		runner.run(input, Options.v().getClasspath(), Options.v().getCallGraphAlgorithm());

		if (Options.v().getCallGraphAlgorithm() != CallgraphAlgorithm.None) {
			Log.info("Call Graph found ... but Ignored ... don't use spark for now!");
		} else {
			Log.info("No Callgraph (use -cg spark if you want one). Improvising!");
		}
		Log.info("Total classes in secene : " + Scene.v().getClasses().size());

		/*
		 * Construct the call graphs for each method.
		 */
		for (SootClass sc : Scene.v().getClasses()) {
			processSootClass(sc);
		}
		/*
		 * Now create one global call graph.
		 */
		MyCallDependencyGraph myCG = new MyCallDependencyGraph(
				this.callDependencyMap);
		myCG.toDot("cg.dot");
		for (SootMethod m : myCG.getHeads()) {
			System.out.println("Entries " + m.getName());
		}
		//TODO: some procedures might be ignored ...
		// ... if their entry is already recursive

		Collection<String> dotfileNames = new LinkedList<String>();
		
		int i = 0;
		// build the icfg...
		for (SootMethod m : myCG.getHeads()) {
			LocalCallGraphBuilder cgb = inlineCallgraphs(m,
					new Stack<Entry<SootMethod, LocalCallGraphBuilder>>());
			if (!cgb.getNodes().isEmpty()) {
				final String filename = "dot/" + String.format("%04d", i++) + "_" + m.getName()+".dot";
				cgb.toDot(filename);				
				dotfileNames.add(filename);
			}
		}

		return dotfileNames;
	}

	private LocalCallGraphBuilder inlineCallgraphs(SootMethod m,
			Stack<Entry<SootMethod, LocalCallGraphBuilder>> callStack) {
		LocalCallGraphBuilder cgb = this.procedureCallGraphs.get(m).duplicate();
		/*
		 * Push the current procedure on the stack so, in case we call it
		 * recursively, we don't start going into an infinite loop.
		 */
		callStack
				.push(new AbstractMap.SimpleEntry<SootMethod, LocalCallGraphBuilder>(
						m, cgb));

		List<InterprocdurcalCallGraphNode> todo = new LinkedList<InterprocdurcalCallGraphNode>(
				cgb.getNodes());
		for (InterprocdurcalCallGraphNode n : todo) {
			for (SootMethod callee : new HashSet<SootMethod>(n.getCallees())) {
				if (this.procedureCallGraphs.containsKey(callee)) {
					n.getCallees().remove(callee);
					LocalCallGraphBuilder recursiveCg = findInStack(callee,
							callStack);
					if (recursiveCg == null) {
						//which mean that this procedure has not been 
						//inline on this path.
						recursiveCg = inlineCallgraphs(callee, callStack);
						// connect all predecessors to the successors of the
						// source of the callee (i.e.,
						// throw away the old source).
						for (InterprocdurcalCallGraphNode pre : n.predessors) {
							for (InterprocdurcalCallGraphNode entry : recursiveCg
									.getSource().successors) {
								pre.connectTo(entry);
							}
						}
						// now for the sink
						if (recursiveCg.getSink() != null) {
							for (InterprocdurcalCallGraphNode ret : n.successors) {
								for (InterprocdurcalCallGraphNode suc : recursiveCg.getSink().predessors) {
									suc.connectTo(ret);
								}
							}
							//now disconnect the old sink.
							for (InterprocdurcalCallGraphNode pre : recursiveCg.getSink().predessors) {
								pre.successors.remove(recursiveCg.getSink());
							}
						}
						/*
						 * each procedure call node is connected to all exceptional sinks that are mentioned in any throws clause
						 * and to the exceptional sink of RuntimeException.
						 * When we inline, we wire the exceptional sinks of the call side to the one of the graph that is being inlined.
						 * This is necessary, because some of the exceptions thrown by the callee might be caught in the caller.
						 */
						
						for (Entry<SootClass, InterprocdurcalCallGraphNode> entry : recursiveCg.getExceptionalSinks().entrySet()) {
							//check if the current node is connected to an exceptional sink that also occurs in the callee.
							//if so, re-wire the predecessors in the callee
							if (cgb.getExceptionalSinks().containsKey(entry.getKey()) && n.successors.contains(cgb.getExceptionalSinks().get(entry.getKey()))) {
//								System.err.println("Found sink for " + entry.getKey().getName());
								InterprocdurcalCallGraphNode esink = entry.getValue();
								for (InterprocdurcalCallGraphNode pre : new HashSet<InterprocdurcalCallGraphNode>(esink.predessors)) {
									pre.successors.remove(esink);
									pre.connectTo(cgb.getExceptionalSinks().get(entry.getKey()));
									esink.predessors.remove(pre);
								}
							} else {
//								System.err.println("No sink for " + entry.getKey().getName());
								//check if there 
								Set<SootClass> thrownSubtype = new HashSet<SootClass>();
								Hierarchy hierarchy = Scene.v().getActiveHierarchy();
								SootClass parent = entry.getKey();
								for (Entry<SootClass, InterprocdurcalCallGraphNode> entry_ : cgb.getExceptionalSinks().entrySet()) {
									if (hierarchy.isClassSubclassOfIncluding(entry_.getKey(), parent) ) {
										thrownSubtype.add(entry_.getKey());
									}
								}
								if (!thrownSubtype.isEmpty()) {									
									for (InterprocdurcalCallGraphNode pre : new HashSet<InterprocdurcalCallGraphNode>(entry.getValue().predessors)) {
										pre.successors.remove(entry.getValue());
										entry.getValue().predessors.remove(pre);
										for (SootClass exception : thrownSubtype) {
											pre.connectTo(cgb.getExceptionalSinks().get(exception));
										}
									}
								} else {									
									//then this guy is not being caught on the caller side and 
									//we have to add a new exceptional sink to cgb
									InterprocdurcalCallGraphNode esink = entry.getValue();
									SootClass exception = entry.getKey();
									for (InterprocdurcalCallGraphNode pre : new HashSet<InterprocdurcalCallGraphNode>(esink.predessors)) {
										pre.successors.remove(esink);
										esink.predessors.remove(pre);
										
										if (!cgb.getExceptionalSinks().containsKey(exception)) {
											InterprocdurcalCallGraphNode node = new InterprocdurcalCallGraphNode();
											node.setLabel("Exception "+exception.getName());
											cgb.getExceptionalSinks().put(exception, node);
										}
										InterprocdurcalCallGraphNode ex = cgb.getExceptionalSinks().get(exception); 
										pre.connectTo(ex);			
									}									
								}
							}
							
						}
						
						
					} else {
						System.err.println("\twoooo Recursive! "
								+ callee.getBytecodeSignature());
						//connect the predecessors of n to the recursive call
						for (InterprocdurcalCallGraphNode pre : n.predessors) {
							for (InterprocdurcalCallGraphNode entry : recursiveCg
									.getSource().successors) {
								pre.connectTo(entry);
							}
						}
						//no need to process the successors because they are already connected.
					}
				} else {
//					System.err
//							.println("\tooo " + callee.getBytecodeSignature());
				}
			}
			if (n.getCallees().isEmpty() && n != cgb.getSource()
					&& n != cgb.getSink()) {
				// then we could inline all calls and we can
				// safely remove the node
				for (InterprocdurcalCallGraphNode pre : n.predessors) {
					pre.successors.remove(n);
				}
				for (InterprocdurcalCallGraphNode suc : n.successors) {
					suc.predessors.remove(n);
				}
				cgb.removeNode(n);
			}
		}
		// pop the current procedure.
		callStack.pop();
		return cgb;
	}

	private LocalCallGraphBuilder findInStack(SootMethod m,
			Stack<Entry<SootMethod, LocalCallGraphBuilder>> callStack) {
		for (Entry<SootMethod, LocalCallGraphBuilder> entry : callStack) {
			if (m == entry.getKey())
				return entry.getValue();
		}
		return null;
	}



	/**
	 * Analyze a single SootClass and transform all its Methods
	 * 
	 * @param sc
	 */
	private void processSootClass(SootClass sc) {
		if (sc.resolvingLevel() < SootClass.SIGNATURES) {
			return;
		}

		if (sc.isApplicationClass()) {
			for (SootMethod sm : sc.getMethods()) {
				processSootMethod(sm);
			}
		}
	}

	private void processSootMethod(SootMethod sm) {
		if (sm.isConcrete()) {
			transformStmtList(sm.retrieveActiveBody());
		}
	}

	/**
	 * Transforms a list of statements
	 * 
	 * @param body
	 *            Body
	 */
	private void transformStmtList(Body body) {
		//eliminate the exceptions first.
//		ExceptionTransformer transformer = new ExceptionTransformer(new NullnessAnalysis(new CompleteUnitGraph(body)));
//		transformer.transform(body);
		
		
		LocalCallGraphBuilder flow = new LocalCallGraphBuilder(body);
		// now collect all methods in ApplicationClasses that can be called from
		// the body.
		Set<SootMethod> calledApplicationMethods = new HashSet<SootMethod>();
		for (InterprocdurcalCallGraphNode n : flow.getNodes()) {
			for (SootMethod m : n.getCallees()) {
				if (m.getDeclaringClass().isApplicationClass()) {
					calledApplicationMethods.add(m);
				}
			}
		}
		callDependencyMap.put(body.getMethod(), calledApplicationMethods);
		this.procedureCallGraphs.put(body.getMethod(), flow);
		
//		flow.toDot("local"+body.getMethod().getName()+body.getMethod().getNumber()+".dot");
	}

}
