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
import java.util.Stack;

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
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.scalar.ForwardFlowAnalysis;


public class LocalCallGraphBuilder extends ForwardFlowAnalysis<Unit, Set<InterprocdurcalCallGraphNode>> {

	private Map<Unit, InterprocdurcalCallGraphNode> nodes = new HashMap<Unit, InterprocdurcalCallGraphNode>();
	private InterprocdurcalCallGraphNode source;
	private InterprocdurcalCallGraphNode sink;
	private JimpleBasedInterproceduralCFG icfg = null;
		
	/**
	 * copy constructor
	 */
	private LocalCallGraphBuilder(DirectedGraph<Unit> graph, Map<Unit, InterprocdurcalCallGraphNode> nodes, InterprocdurcalCallGraphNode source, InterprocdurcalCallGraphNode sink) {
		super(graph);
		Map<InterprocdurcalCallGraphNode, InterprocdurcalCallGraphNode> clones = new HashMap<InterprocdurcalCallGraphNode, InterprocdurcalCallGraphNode>();
		//first clone all nodes
		for (Entry<Unit, InterprocdurcalCallGraphNode> entry : nodes.entrySet()) {
			InterprocdurcalCallGraphNode clone = entry.getValue().duplicate();
			clones.put(entry.getValue(), clone);
			this.nodes.put(entry.getKey(), clone);
		}
		clones.put(source, source.duplicate());
		if (sink!=null) {
			clones.put(sink, sink.duplicate());
		}
		
		//now connect the cloned nodes.
		for (Entry<InterprocdurcalCallGraphNode, InterprocdurcalCallGraphNode> entry : clones.entrySet()) {
			for (InterprocdurcalCallGraphNode succ : entry.getKey().getSuccessors()) {					
				entry.getValue().connectTo(clones.get(succ));
			}
		}
		this.source = clones.get(source);
		if (sink!=null) this.sink = clones.get(sink);
	}
	
	public LocalCallGraphBuilder duplicate() {
		return new LocalCallGraphBuilder(this.graph, this.nodes, this.source, this.sink);
	}
		
	public LocalCallGraphBuilder(DirectedGraph<Unit> graph, JimpleBasedInterproceduralCFG icfg) {
		super(graph);
		this.icfg = icfg;
		
		this.source = new InterprocdurcalCallGraphNode();
		this.source.setLabel("source");		
		
		this.doAnalysis();
		// generate a unique sink.
		boolean sinkConnected = false;
		this.sink = new InterprocdurcalCallGraphNode();
		this.sink.setLabel("sink");
		for (Entry<Unit, InterprocdurcalCallGraphNode> entry : this.nodes.entrySet()) {
			InterprocdurcalCallGraphNode n = entry.getValue();
			if (n.getSuccessors().isEmpty()) {
				n.connectTo(sink);
				sinkConnected = true;
			}
		}
		if (!sinkConnected) {
			this.sink=null;
		}
	}
	
	public InterprocdurcalCallGraphNode getSource() {
		return this.source;
	}

	public InterprocdurcalCallGraphNode getSink() {
		return this.sink;
	}

	
	public Set<InterprocdurcalCallGraphNode> getNodes() {
		Set<InterprocdurcalCallGraphNode> res = new HashSet<InterprocdurcalCallGraphNode>();
		res.add(source);
		res.addAll(this.nodes.values());
		if (sink!=null) {
			res.add(sink);
		}
		return res;
	}
	
	@Override
	protected void flowThrough(Set<InterprocdurcalCallGraphNode> in, Unit u, Set<InterprocdurcalCallGraphNode> out) {

		Set<SootMethod> callees = findCallees(u);
		if (callees.isEmpty()) {
			// then in == out
			out.addAll(in);
		} else {
			InterprocdurcalCallGraphNode n;
			if (this.nodes.containsKey(u)) {
				n = this.nodes.get(u);
			} else {
				n = new InterprocdurcalCallGraphNode();
				n.setCallees(callees);
				this.nodes.put(u, n);
			}
			for (InterprocdurcalCallGraphNode pre : in) {
				pre.connectTo(n);
				out.clear();
				out.add(n);
			}
		}
	}

	public void removeNode(InterprocdurcalCallGraphNode n) {
		Map<Unit, InterprocdurcalCallGraphNode> tmp = new HashMap<Unit, InterprocdurcalCallGraphNode>(this.nodes);
		
		for (Entry<Unit, InterprocdurcalCallGraphNode> entry : tmp.entrySet() ){
			if (entry.getValue()==n) {
				this.nodes.remove(entry.getKey());
			}
		}
	}
	
	@Override
	protected void copy(Set<InterprocdurcalCallGraphNode> from, Set<InterprocdurcalCallGraphNode> to) {
		// TODO Auto-generated method stub
		to.clear();
		to.addAll(from);
	}

	@Override
	protected void merge(Set<InterprocdurcalCallGraphNode> in1, Set<InterprocdurcalCallGraphNode> in2, Set<InterprocdurcalCallGraphNode> out) {
		out.clear();
		out.addAll(in1);
		out.addAll(in2);
	}

	@Override
	protected Set<InterprocdurcalCallGraphNode> newInitialFlow() {
		Set<InterprocdurcalCallGraphNode> init = new HashSet<InterprocdurcalCallGraphNode>();
		init.add(this.source);
		return init;
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
	
	public void toDot(String filename) {
		//first collect all reachable nodes.
		Stack<InterprocdurcalCallGraphNode> todo = new Stack<InterprocdurcalCallGraphNode>();
		todo.push(source);
		Set<InterprocdurcalCallGraphNode> done = new HashSet<InterprocdurcalCallGraphNode>();
		while (!todo.isEmpty()) {
			InterprocdurcalCallGraphNode current = todo.pop();
			done.add(current);
			for (InterprocdurcalCallGraphNode suc : current.successors) {
				if (!todo.contains(suc) && !done.contains(suc)) {
					todo.push(suc);
				}
			}
		}
		
		File fpw = new File(filename);
		try (PrintWriter pw = new PrintWriter(fpw, "utf-8");) {
			pw.println("digraph dot {");
			for (InterprocdurcalCallGraphNode n : done) {
				String shape = " shape=oval ";
				pw.println("\t\"" + n.getLabel() + "\" " + "[label=\""
						+ n.getLabel() + "\" " + shape + "];\n");
			}
			pw.append("\n");
			for (InterprocdurcalCallGraphNode from : done) {
				for (InterprocdurcalCallGraphNode to : from.getSuccessors()) {
					pw.append("\t\"" + from.getLabel() + "\" -> \""
							+ to.getLabel() + "\";\n");					
				}
				
			}
			pw.println("}");
		} catch (IOException e) {
			e.printStackTrace();
		}
	}	
	
}