package de.uka.ilkd.key.specgen.verificationrelationsystem.graph;

import de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation.Delta;
import de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation.Phi;

public class VerificationRelationGraphEdge {

	private VerificationRelationGraphNode mySource;
	private Phi myCondition;
	private Delta myChange;
	private VerificationRelationGraphNode myDestination;
	
	public VerificationRelationGraphEdge(VerificationRelationGraphNode source, Phi condition, Delta change, VerificationRelationGraphNode destination) {
		mySource      = source;
		myCondition   = condition;
		myChange      = change;
		myDestination = destination;
	}
	
	public VerificationRelationGraphNode getSource() {
		return mySource;
	}
	public Phi getCondition() {
		return myCondition;
	}
	public Delta getChange() {
		return myChange;
	}
	public VerificationRelationGraphNode getDestination() {
		return myDestination;
	}
	
	@Override
	public String toString() {
		String result = "";
		result = result + "(" + mySource + "-[" + myCondition + "," + myChange + "]->" + myDestination + ")";
		return result;
	}
	
}
