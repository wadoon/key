package de.uka.ilkd.key.specgen.strategy;

import de.uka.ilkd.key.specgen.generator.SpecGenerator;
import de.uka.ilkd.key.specgen.verificationrelationsystem.graph.VerificationRelationGraph;

public abstract class Strategy {
	
	protected abstract SpecGenerator selectAnalysis(VerificationRelationGraph graph);
	
	protected abstract boolean done(VerificationRelationGraph graph);
	
	public void run(VerificationRelationGraph graph) {
		while(!done(graph)) {
			SpecGenerator currentAnalysis = selectAnalysis(graph);
		}
	}
	
}
