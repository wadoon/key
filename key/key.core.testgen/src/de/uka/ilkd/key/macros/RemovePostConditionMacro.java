package de.uka.ilkd.key.macros;

import java.util.HashSet;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

public final class RemovePostConditionMacro extends StrategyProofMacro {
	
	private final PostconditionRuleFilter ruleFilter;
	
	public RemovePostConditionMacro() {
		super();
		ruleFilter = new PostconditionRuleFilter();
	}
	
	private class PostconditionRuleFilter implements RuleFilter {
		
		private HashSet<String> allowedRulesNames;		
		{
			allowedRulesNames = new HashSet<String>();			
			allowedRulesNames.add("impRight");
			allowedRulesNames.add("hide_right");
		}

		@Override
		public boolean filter(Rule rule) {
			return allowedRulesNames.contains(rule.name().toString());
		}
		
	}
	
	private class RemovePostConditionStrategy implements Strategy{

		@Override
		public Name name() {
			return new Name("remove Postcondition");
		}

		@Override
		public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
			if (app.rule().name().toString().equals("hide_right")) {
				System.out.println(app.rule().name().toString());
			}
//			System.out.println(app.rule().name().toString());
			if (ruleFilter.filter(app.rule())) {
				if(app.rule().name().toString().equals("impRight")) {
					return NumberRuleAppCost.create(0);
				}
				else {
					return NumberRuleAppCost.create(0);
				}
			}
			return TopRuleAppCost.INSTANCE;
		}

		@Override
		public boolean isStopAtFirstNonCloseableGoal() {
			return false;
		}	

		@Override
		public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
			if (app.rule().name().toString().equals("hide_right")) {
				System.out.println(app.rule().name().toString());
			}
			if (ruleFilter.filter(app.rule())) {
//				System.out.println(app.rule().name());
				return true;
			}
			return false;
		}

		@Override
		public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal, RuleAppCostCollector collector) {
			// TODO Auto-generated method stub
			
		}
	}

	@Override
	public String getName() {
		return "remove postcondition";
	}

	@Override
	public String getCategory() {
		return null;
	}

	@Override
	public String getDescription() {
		return "removes postcondition from proof";
	}

	@Override
	protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
		return new RemovePostConditionStrategy();
	}

	
}
