package de.uka.ilkd.key.specgen.verificationrelationsystem.graph;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation.Delta;
import de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation.Phi;
import de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation.Placeholder;
import de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation.VerificationRelation;

public class VerificationRelationGraphGenerator {

	private static VerificationRelationGraphGenerator instance;

	private VerificationRelationGraphGenerator() {}
	
	public static VerificationRelationGraphGenerator getInstance() {
		if(instance == null) {
			instance = new VerificationRelationGraphGenerator();
		}
		return instance;
	}
	
	public VerificationRelationGraph generate(Set<VerificationRelation> verificationRelations) {
		// compute placeholder symbols
		Set<Placeholder> placeholders = new HashSet<>();
		for(VerificationRelation currentVerificationRelation : verificationRelations) {
			Placeholder source = currentVerificationRelation.getSourcePlaceholder();
			Placeholder desination = currentVerificationRelation.getDestinationPlaceholder();
			placeholders.add(source);
			placeholders.add(desination);
		}
		Map<Placeholder, VerificationRelationGraphNode> placeholderToNode = new HashMap<>();
		// compute nodes
		Set<VerificationRelationGraphNode> nodes = new HashSet<>();
		for(Placeholder currentPlaceholder : placeholders) {
			VerificationRelationGraphNode currentNode = new VerificationRelationGraphNode(currentPlaceholder);
			placeholderToNode.put(currentPlaceholder, currentNode);
			nodes.add(currentNode);
		}
		// compute edges
		Set<VerificationRelationGraphEdge> edges = new HashSet<>();
		for(VerificationRelation currentVerificationRelation : verificationRelations) {
			Placeholder source = currentVerificationRelation.getSourcePlaceholder();
			Placeholder desination = currentVerificationRelation.getDestinationPlaceholder();
			VerificationRelationGraphNode sourceNode = placeholderToNode.get(source);
			VerificationRelationGraphNode destinationNode = placeholderToNode.get(desination);
			Phi condition = currentVerificationRelation.getCondition();
			Delta change = currentVerificationRelation.getChange();
			VerificationRelationGraphEdge currentEdge = new VerificationRelationGraphEdge(sourceNode, condition, change, destinationNode);
			sourceNode.addOutgoingEdge(currentEdge);
			destinationNode.addIncomingEdge(currentEdge);;
			edges.add(currentEdge);
		}
		return new VerificationRelationGraph(nodes, edges);
	}
	
}
