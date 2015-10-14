/**
 * 
 */
package api_learner.soot;

import java.util.AbstractMap;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.toolkits.ide.icfg.JimpleBasedInterproceduralCFG;
import soot.toolkits.exceptions.UnitThrowAnalysis;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.ExceptionalUnitGraph;
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

	private JimpleBasedInterproceduralCFG icfg = null;

	Map<SootMethod, Set<SootMethod>> callDependencyMap = new HashMap<SootMethod, Set<SootMethod>>();
	Map<SootMethod, LocalCallGraphBuilder> procedureCallGraphs = new HashMap<SootMethod, LocalCallGraphBuilder>();

	/**
	 * Generates the call graph for given input
	 * 
	 * @param input
	 *            either the root folder of a set of class files or a jarfile
	 * @return true if the input could be analyzed and false otherwise.
	 */
	public boolean run(String input) {

		// run soot to load all classes.
		SootRunner runner = new SootRunner();
		if (!runner.run(input)) {
			return false;
		}

		if (Options.v().getCallGraphAlgorithm() != CallgraphAlgorithm.None) {
			Log.info("Call Graph found");
			icfg = new JimpleBasedInterproceduralCFG();
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

		int i = 0;
		// build the icfg...
		for (SootMethod m : myCG.getHeads()) {
			LocalCallGraphBuilder cgb = inlineCallgraphs(m,
					new Stack<Entry<SootMethod, LocalCallGraphBuilder>>());
			if (!cgb.getNodes().isEmpty()) {
				cgb.toDot("dot/" + String.format("%04d", i++) + "_" + m.getName()+".dot");
			}
		}

		return true;
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
		DirectedGraph<Unit> cfg;
		if (this.icfg != null) {
			cfg = this.icfg.getOrCreateUnitGraph(body);			
		} else {
			cfg = new ExceptionalUnitGraph(body, UnitThrowAnalysis.v());
		}
		
		LocalCallGraphBuilder flow = new LocalCallGraphBuilder(cfg, this.icfg);
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
