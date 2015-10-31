package api_learner.soot;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import soot.Body;
import soot.Hierarchy;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Trap;
import soot.Unit;
import soot.Value;
import soot.JastAddJ.CastExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.DynamicInvokeExpr;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.ThrowStmt;
import soot.toolkits.graph.CompleteUnitGraph;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.scalar.ForwardFlowAnalysis;
import api_learner.Options;


public class LocalCallGraphBuilder extends ForwardFlowAnalysis<Unit, Set<InterprocdurcalCallGraphNode>> {

	private Map<Unit, InterprocdurcalCallGraphNode> nodes = new HashMap<Unit, InterprocdurcalCallGraphNode>();
	private InterprocdurcalCallGraphNode source;
	private InterprocdurcalCallGraphNode sink;
	private final Map<SootClass, InterprocdurcalCallGraphNode> exceptionalSinks = new HashMap<SootClass, InterprocdurcalCallGraphNode>();
		
	/**
	 * copy constructor
	 */
	private LocalCallGraphBuilder(DirectedGraph<Unit> graph, Map<Unit, InterprocdurcalCallGraphNode> nodes, InterprocdurcalCallGraphNode source, InterprocdurcalCallGraphNode sink, Map<SootClass, InterprocdurcalCallGraphNode> exSinks) {
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
				
		for (Entry<SootClass, InterprocdurcalCallGraphNode> entry : exSinks.entrySet()) {
			InterprocdurcalCallGraphNode clonedSink = entry.getValue().duplicate();
			exceptionalSinks.put(entry.getKey(), clonedSink);
			clones.put(entry.getValue(), clonedSink);
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
		return new LocalCallGraphBuilder(this.graph, this.nodes, this.source, this.sink, this.exceptionalSinks);
	}

	private Body body = null;
	
	public LocalCallGraphBuilder(Body body) {
		super(new CompleteUnitGraph(body));
		this.body = body;
		
		this.source = new InterprocdurcalCallGraphNode();
		this.source.setLabel("source");		
		this.sink = new InterprocdurcalCallGraphNode();
		this.sink.setLabel("sink");
		
		this.doAnalysis();
		// generate a unique sink.
		if (this.sink.predessors.isEmpty()) {
			this.sink=null;
		}
	}
	
	public InterprocdurcalCallGraphNode getSource() {
		return this.source;
	}

	public InterprocdurcalCallGraphNode getSink() {
		return this.sink;
	}

	/**
	 * Its important that we return the original, so we can add stuff to it later.
	 * @return
	 */
	public Map<SootClass, InterprocdurcalCallGraphNode> getExceptionalSinks() {
		return exceptionalSinks;
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
		if (this.graph.getHeads().contains(u)) {
			in.add(this.source);
		}
				
		Set<SootMethod> callees = findCallees(u);
		if (callees.isEmpty()) {
			// then in == out
			out.clear();
			if (u instanceof ReturnVoidStmt || u instanceof ReturnStmt) {
				for (InterprocdurcalCallGraphNode pre : in) {
					pre.connectTo(this.sink);
				}
				return;
			} 
			
			if (u instanceof ThrowStmt) {				
				RefType thrownType = (RefType)((ThrowStmt)u).getOp().getType();
				SootClass sc = thrownType.getSootClass();
				connectUncaughtToExceptionalSink(in, u, sc);
				return;
			} 
			
			addPossibleExceptionSinks(in, u);
			
			out.addAll(in);
			return;
			
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
			}
			out.clear();
			out.add(n);
			
			//Connect n to potential uncaught exceptional termination.
			//TODO: This is a crude over-approximation 
			Set<SootClass> thrownExceptions = new HashSet<SootClass>();
			for (SootMethod sm : callees) {
				thrownExceptions.addAll(sm.getExceptions());
			}
			thrownExceptions.add(Scene.v().getSootClass("java.lang.RuntimeException"));
			for (SootClass ex : thrownExceptions) {
				connectUncaughtToExceptionalSink(out, u, ex);
			}
			
			return;
		}
	}

	private void addPossibleExceptionSinks(Set<InterprocdurcalCallGraphNode> in, Unit u) {
		Stmt s = (Stmt)u;
		if (s.containsArrayRef()) {			
			//TODO: check if this is always safe.
			connectUncaughtToExceptionalSink(in, u, Scene.v().getSootClass("java.lang.ArrayIndexOutOfBoundsException"));
		}
		
		if (s.containsFieldRef() && s.getFieldRef() instanceof InstanceFieldRef) {
			//TODO: check if this is always safe.
			connectUncaughtToExceptionalSink(in, u, Scene.v().getSootClass("java.lang.NullPointerException"));
		}
		
		if (s instanceof DefinitionStmt && ((DefinitionStmt)s).getRightOp() instanceof CastExpr) {
			//TODO: check if this is always safe.
			connectUncaughtToExceptionalSink(in, u, Scene.v().getSootClass("java.lang.ClassCastException"));	
		}
		
	}
	
	private void connectUncaughtToExceptionalSink(Set<InterprocdurcalCallGraphNode> nodes, Unit u, SootClass exception) {
		Hierarchy hierarchy = Scene.v().getActiveHierarchy();
		boolean caught = false;
		for (Trap trap : getTrapsGuardingUnit(u, body)) {
			if (hierarchy.isClassSubclassOfIncluding(exception, trap.getException())) {
				caught = true; break;
			}
		}
		if (!caught) {
			if (!exceptionalSinks.containsKey(exception)) {		
				InterprocdurcalCallGraphNode node = new InterprocdurcalCallGraphNode();
				node.setLabel("Exception "+exception.getName());
				exceptionalSinks.put(exception, node);
			}
			InterprocdurcalCallGraphNode exceptionSink = exceptionalSinks.get(exception);
								
			for (InterprocdurcalCallGraphNode pre : nodes) {
				pre.connectTo(exceptionSink);
			}
			
		}
	}
	
	
	
	
	protected List<Trap> getTrapsGuardingUnit(Unit u, Body b) {
		List<Trap> result = new LinkedList<Trap>();
		for (Trap t : b.getTraps()) {
			Iterator<Unit> it = b.getUnits().iterator(t.getBeginUnit(), t.getEndUnit());
			while (it.hasNext()) {
				if (u.equals(it.next())) {
					result.add(t);
				}
			}
		}
		return result;
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
//		init.add(this.source);
		return init;
	}

	private Set<SootMethod> findCallees(Unit u) {
		Set<SootMethod> callees = new HashSet<SootMethod>();
		
//		if (this.icfg!=null) {
//			//if we have the icfg, its simple.
//			callees.addAll(this.icfg.getCalleesOfCallAt(u));
//			return callees;
//		}
		
		if (u instanceof Stmt) {
			Stmt s = (Stmt) u;
			if (s.containsInvokeExpr()) {
				InvokeExpr invoke = s.getInvokeExpr();
				if (invoke instanceof DynamicInvokeExpr) {
					DynamicInvokeExpr ivk = (DynamicInvokeExpr) invoke;
					// TODO: 
					System.err.println("no idea how to handle DynamicInvoke: " + ivk);
					callees.add(ivk.getMethod());
				} else if (invoke instanceof StaticInvokeExpr) {					
					StaticInvokeExpr ivk = (StaticInvokeExpr) invoke;
					if (ivk.getMethod().hasActiveBody() || isInterestingProcedure(ivk.getMethod())) {
						callees.add(ivk.getMethod());	
					} else {
						// do nothing
					}
				} else if (invoke instanceof InstanceInvokeExpr) {
					InstanceInvokeExpr ivk = (InstanceInvokeExpr) invoke;
					callees.addAll(resolveVirtualCall(s, ivk.getBase(),
							ivk.getMethod()));
				}
			}
		}
		return callees;
	}

	
	private boolean isInterestingProcedure(SootMethod callee) {
		SootClass sc = callee.getDeclaringClass();
		if (Options.v().getNamespace()!=null && !Options.v().getNamespace().isEmpty()) {
			String fullClassName = callee.getDeclaringClass().getPackageName() + "." + callee.getDeclaringClass().getName();
			if (fullClassName.contains(Options.v().getNamespace())) {
				return true;
			} else {
				//do nothing
			}
		} else {			
			if (sc.isJavaLibraryClass()) {
				//if no namespace is given, we consider any jdk call interesting.
				//just for debugging
				return true;
			}
		}
		return false;
	}
	
	private Set<SootMethod> resolveVirtualCall(Stmt s, Value base,
			SootMethod callee) {
		Set<SootMethod> res = new HashSet<SootMethod>();
		SootClass sc = callee.getDeclaringClass();
		
		if (callee.hasActiveBody()) {
			//TODO: and add all overriding methods
			res.add(callee);
		} else {
			if (!isInterestingProcedure(callee)) {
//				System.err.println(callee.getSignature() + " is not interesting");
				// if we neither have a body for the procedure, nor the are
				// interested in the procedure, we just throw it away by returning
				// the empty set.
				return new HashSet<SootMethod>();
			}
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
				if (sub.declaresMethod(callee.getName(), callee.getParameterTypes(), callee.getReturnType())) {
					res.add(sub.getMethod(callee.getName(), callee.getParameterTypes(), callee.getReturnType()));
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
				pw.println("\t\"" + n.getUniqueLabel() + "\" " + "[label=\""
						+ n.getLabel() + "\" " + shape + "];\n");
			}
			pw.append("\n");
			for (InterprocdurcalCallGraphNode from : done) {
				for (InterprocdurcalCallGraphNode to : from.getSuccessors()) {
					pw.append("\t\"" + from.getUniqueLabel() + "\" -> \""
							+ to.getUniqueLabel() + "\";\n");					
				}
				
			}
			pw.println("}");
		} catch (IOException e) {
			e.printStackTrace();
		}
	}	
	
}