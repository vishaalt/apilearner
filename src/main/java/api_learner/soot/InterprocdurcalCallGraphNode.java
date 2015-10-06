package api_learner.soot;

import java.util.HashSet;
import java.util.Set;
import java.util.UUID;

import soot.SootMethod;


public class InterprocdurcalCallGraphNode {
	
	Set<SootMethod> callees = new HashSet<SootMethod>();
	public Set<InterprocdurcalCallGraphNode> successors = new HashSet<InterprocdurcalCallGraphNode>();
	public Set<InterprocdurcalCallGraphNode> predessors = new HashSet<InterprocdurcalCallGraphNode>();
	private String label;
	private String id;

	/**
	 * default constructor
	 */
	public InterprocdurcalCallGraphNode() {
		
	}	
	
	public void setCallees(Set<SootMethod> callees) {
		this.label = callees.iterator().next().getSignature();
		this.id = UUID.randomUUID().toString();
		this.callees = callees;
	}

	public void connectTo(InterprocdurcalCallGraphNode succ) {
		this.successors.add(succ);
		succ.predessors.add(this);
	}

	public Set<InterprocdurcalCallGraphNode> getSuccessors() {
		return this.successors;
	}

	public Set<SootMethod> getCallees() {
		return this.callees;
	}

	public String getLabel() {
		return label;
	}

	public String getUniqueLabel() {
		return label+"__"+this.id;
	}

	
	public void setLabel(String label) {
		this.label = label;
		this.id = UUID.randomUUID().toString();
	}
	
	
	public InterprocdurcalCallGraphNode duplicate() {
		return new InterprocdurcalCallGraphNode(this.label, this.callees);
	}
	/**
	 * copy constructor
	 * @param label
	 * @param callees
	 */
	private InterprocdurcalCallGraphNode(String label, Set<SootMethod> callees) {
		this.label = label;
		this.id = UUID.randomUUID().toString();
		this.callees.addAll(callees);
	}
	
}