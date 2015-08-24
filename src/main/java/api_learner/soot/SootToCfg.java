/**
 * 
 */
package api_learner.soot;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.DynamicInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.toolkits.ide.icfg.JimpleBasedInterproceduralCFG;
import soot.toolkits.exceptions.UnitThrowAnalysis;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.scalar.ForwardFlowAnalysis;
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

		for (SootClass sc : Scene.v().getClasses()) {
			processSootClass(sc);
		}

		return true;
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
		if (this.icfg!=null) {
			cfg = this.icfg.getOrCreateUnitGraph(body);
		} else {
			cfg = new ExceptionalUnitGraph(body,
					UnitThrowAnalysis.v());
		}
		System.err.println(body.getMethod().getSignature());
		MyFlow flow = new MyFlow(cfg);
		toDot(body.getMethod().getName()+body.getMethod().getNumber()+".dot", flow.getNodes());
	}
	
	
	public void toDot(String filename, Set<Node> nodes) {
		File fpw = new File(filename);
		try (PrintWriter pw = new PrintWriter(fpw, "utf-8");) {
			pw.println("digraph dot {");
			for (Node n : nodes) {
				String shape = " shape=oval ";
				pw.println("\t\"" + n.getLabel() + "\" " + "[label=\""
						+ n.getLabel() + "\" " + shape + "];\n");
			}
			pw.append("\n");
			for (Node from : nodes) {
				for (Node to : from.getSuccessors()) {
					pw.append("\t\"" + from.getLabel() + "\" -> \""
							+ to.getLabel() + "\";\n");					
				}
				
			}
			pw.println("}");
		} catch (IOException e) {
			e.printStackTrace();
		}
	}	
	
	private static int hack_counter = 0;
	
	public static class Node {
		
		Set<SootMethod> callees = new HashSet<SootMethod>();
		Set<Node> successors = new HashSet<Node>();
		private String label;

		public void setCallees(Set<SootMethod> callees) {
			this.label = callees.iterator().next().getName()+ "__"+(hack_counter++);
			this.callees = callees;
		}

		public void connectTo(Node succ) {
			this.successors.add(succ);
		}

		public Set<Node> getSuccessors() {
			return this.successors;
		}

		public Set<SootMethod> getCallees() {
			return this.callees;
		}

		public String getLabel() {
			return label;
		}

		public void setLabel(String label) {
			this.label = label;
		}
	}

	public class MyFlow extends ForwardFlowAnalysis<Unit, Set<Node>> {

		private Map<Unit, Node> nodes = new HashMap<Unit, Node>();
		private final Node source, sink;

		public MyFlow(DirectedGraph<Unit> graph) {
			super(graph);
			this.source = new Node();
			this.source.setLabel("source");
			
			this.doAnalysis();
			// generate a unique sink.
			this.sink = new Node();
			this.sink.setLabel("sink");
			for (Entry<Unit, Node> entry : this.nodes.entrySet()) {
				Node n = entry.getValue();
				if (n.getSuccessors().isEmpty()) {
					n.connectTo(sink);
				}
			}
		}
		
		public Set<Node> getNodes() {
			Set<Node> res = new HashSet<Node>();
			res.addAll(this.nodes.values());
			return res;
		}
		
		@Override
		protected void flowThrough(Set<Node> in, Unit u, Set<Node> out) {

			Set<SootMethod> callees = findCallees(u);
			if (callees.isEmpty()) {
				// then in == out
				out.addAll(in);
			} else {
				Node n;
				if (this.nodes.containsKey(u)) {
					n = this.nodes.get(u);
				} else {
					n = new Node();
					n.setCallees(callees);
					this.nodes.put(u, n);
				}
				for (Node pre : in) {
					pre.connectTo(n);
					out.clear();
					out.add(n);
				}
			}
		}

		@Override
		protected void copy(Set<Node> from, Set<Node> to) {
			// TODO Auto-generated method stub
			to.clear();
			to.addAll(from);
		}

		@Override
		protected void merge(Set<Node> in1, Set<Node> in2, Set<Node> out) {
			out.clear();
			out.addAll(in1);
			out.addAll(in2);
		}

		@Override
		protected Set<Node> newInitialFlow() {
			Set<Node> init = new HashSet<Node>();
			init.add(this.source);
			return init;
		}

	}

	private Set<SootMethod> findCallees(Unit u) {
		Set<SootMethod> callees = new HashSet<SootMethod>();
		
		if (this.icfg!=null) {
			//if we have the icfg, its simple.
			callees.addAll(this.icfg.getCalleesOfCallAt(u));
			return callees;
		}
		
		if (u instanceof Stmt) {
			Stmt s = (Stmt) u;
			if (s.containsInvokeExpr()) {
				InvokeExpr invoke = s.getInvokeExpr();
				if (invoke instanceof DynamicInvokeExpr) {
					DynamicInvokeExpr ivk = (DynamicInvokeExpr) invoke;
					// TODO: Log.error("no idea how to handle DynamicInvoke: " +
					// ivk);
					callees.add(ivk.getMethod());
				} else if (invoke instanceof InterfaceInvokeExpr) {
					InterfaceInvokeExpr ivk = (InterfaceInvokeExpr) invoke;
					callees.addAll(resolveVirtualCall(s, ivk.getBase(),
							ivk.getMethod()));
				} else if (invoke instanceof SpecialInvokeExpr) {
					SpecialInvokeExpr ivk = (SpecialInvokeExpr) invoke;
					// TODO: Log.info("not sure how to treat constructors");
					callees.add(ivk.getMethod());
				} else if (invoke instanceof StaticInvokeExpr) {
					StaticInvokeExpr ivk = (StaticInvokeExpr) invoke;
					callees.add(ivk.getMethod());
				} else if (invoke instanceof VirtualInvokeExpr) {
					VirtualInvokeExpr ivk = (VirtualInvokeExpr) invoke;
					callees.addAll(resolveVirtualCall(s, ivk.getBase(),
							ivk.getMethod()));
				}
			}
		}
		return callees;
	}

	private Set<SootMethod> resolveVirtualCall(Stmt s, Value base,
			SootMethod callee) {
		Set<SootMethod> res = new HashSet<SootMethod>();
		SootClass sc = callee.getDeclaringClass();

		if (!sc.isJavaLibraryClass()) {
			// don't care about non application API calls.
			res.add(callee);
			return res;
		}

		if (callee.hasActiveBody()) {
			res.add(callee);
		}

		Collection<SootClass> possibleClasses;
		if (sc.isInterface()) {
			possibleClasses = Scene.v().getFastHierarchy()
					.getAllImplementersOfInterface(sc);
		} else {
			possibleClasses = Scene.v().getFastHierarchy().getSubclassesOf(sc);
		}
		for (SootClass sub : possibleClasses) {
			if (sub.resolvingLevel() < SootClass.SIGNATURES) {
				// Log.error("Not checking subtypes of " + sub.getName());
				// Then we probably really don't care.
			} else {
				if (sub.declaresMethod(callee.getSubSignature())) {
					res.add(sub.getMethod(callee.getSubSignature()));
				}
			}
		}

		if (res.isEmpty()) {
			res.add(callee);
		}
		return res;
	}

}
