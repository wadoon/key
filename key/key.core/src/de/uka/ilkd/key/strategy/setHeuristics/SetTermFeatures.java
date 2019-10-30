package de.uka.ilkd.key.strategy.setHeuristics;

import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.strategy.StaticFeatureCollection;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

public class SetTermFeatures extends StaticFeatureCollection {

	public SetTermFeatures(SetLDT sets) {
		single = sets.getSingle();
		
		singleF = op(single);
	}

	final Function single;
	
	final TermFeature singleF;
}
