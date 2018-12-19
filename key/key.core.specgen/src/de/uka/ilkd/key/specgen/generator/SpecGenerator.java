package de.uka.ilkd.key.specgen.generator;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.specgen.verificationrelationsystem.graph.VerificationRelationGraph;

public interface SpecGenerator {
	
	public ImmutableList<VerificationRelationGraph> admissableSubgraphs(VerificationRelationGraph graph);
	
	public void analyse(VerificationRelationGraph graph);

}
