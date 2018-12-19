package de.uka.ilkd.key.specgen.verificationrelationsystem.graph;

import java.util.HashSet;
import java.util.Set;

public class VerificationRelationGraph {
	
	private Set<VerificationRelationGraphNode> myNodes;
	private Set<VerificationRelationGraphEdge> myEdges;
	
	public VerificationRelationGraph(Set<VerificationRelationGraphNode> nodes, Set<VerificationRelationGraphEdge> edges) {
		myNodes = nodes;
		myEdges = edges;
	}
	public VerificationRelationGraph() {
		this(new HashSet<>(), new HashSet<>());
	}
	
	public void addNode(VerificationRelationGraphNode node) {
		myNodes.add(node);
	}
	public void addEdge(VerificationRelationGraphEdge edge) {
		myEdges.add(edge);
	}
	
	public Set<VerificationRelationGraphNode> getNodes() {
		return myNodes;
	}
	
	public Set<VerificationRelationGraphEdge> getEdges() {
		return myEdges;
	}
	public boolean instantiationFound() {
		// TODO Auto-generated method stub
		return false;
	}
	
}
