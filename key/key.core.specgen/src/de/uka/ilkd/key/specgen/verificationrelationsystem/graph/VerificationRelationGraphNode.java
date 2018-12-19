package de.uka.ilkd.key.specgen.verificationrelationsystem.graph;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation.Placeholder;

public class VerificationRelationGraphNode {

	private Placeholder myPlaceholder;
	private Set<VerificationRelationGraphEdge> myIncomingEdges;
	private Set<VerificationRelationGraphEdge> myOutgoingEdges;
	
	public VerificationRelationGraphNode(Placeholder placeholder) {
		myPlaceholder = placeholder;
		myIncomingEdges = new HashSet<>();
		myOutgoingEdges = new HashSet<>();
	}
	
	public void addIncomingEdge(VerificationRelationGraphEdge edge) {
		myIncomingEdges.add(edge);
	}
	public void addOutgoingEdge(VerificationRelationGraphEdge edge) {
		myOutgoingEdges.add(edge);
	}
	
	public Placeholder getPlaceholder() {
		return myPlaceholder;
	}
	public Set<VerificationRelationGraphEdge> getIncomingEdges() {
		return myIncomingEdges;
	}
	public Set<VerificationRelationGraphEdge> getOutgoingEdges() {
		return myOutgoingEdges;
	}
	
	@Override
	public String toString() {
		String result = "";
		result = result + myPlaceholder;
		return result;
	}
	
}
