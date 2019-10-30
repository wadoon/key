package de.uka.ilkd.key.strategy.setHeuristics;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.feature.Feature;

public class SetAssocFeature implements Feature {

	public SetAssocFeature() {
		// TODO Auto-generated constructor stub
	}

	public static final int OFFSET = 1000; //TODO might need to be changed
	
	@Override
	public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
		RuleAppCost result = NumberRuleAppCost.create(OFFSET + pos.depth());
		if(app.rule().name().equals("union_assoc")) {
			//TODO make infinite if the target term contains intersectiion or if the left arg of the top level union is an union. 
			
		}else if(app.rule().name().equals("union_assoc2")) {
			//TODO make infinite if the target term contains intersectiion
			
		}else if(app.rule().name().equals("intersect_assoc")) {
			//TODO make infinite if the left arg of the top level intersect is an intersect.
			
		}else if(app.rule().name().equals("intersect_assoc2")) {
			
		}
		return null;
	}

}
