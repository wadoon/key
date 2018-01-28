package de.uka.ilkd.key.macros;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

public final class RemovePostConditionMacro extends StrategyProofMacro {
	
	private static class RemovePostconditionStrategy extends FilterStrategy{

		private static final Name NAME = new Name(
				RemovePostconditionStrategy.class.getSimpleName());
		private static final Set<String> removeRules;
		private static final int maxImpRight = 1;
		
		static {
			removeRules = new HashSet<String>();
			RemovePostconditionStrategy.removeRules.add("impRight");
			RemovePostconditionStrategy.removeRules.add("hide_right");
		}

		private static boolean isRemoveRule(Rule rule) {
			if (rule == null) {
				return false;
			}
			final String name = rule.name().toString();
			return RemovePostconditionStrategy.removeRules.contains(name);
		}

		public RemovePostconditionStrategy(Strategy delegate) {
			super(delegate);
		}

		@Override
		public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio,
		        Goal goal) {
			if (RemovePostconditionStrategy.isRemoveRule(app.rule())) {
				if (app.rule().name().toString().equals("hide_right")) {
					return NumberRuleAppCost.create(100);
				}
				return NumberRuleAppCost.create(10);
			} else {
				return TopRuleAppCost.INSTANCE;
			}
//			return super.computeCost(app, pio, goal);
		}
		
		@Override
		public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
			
			if (RemovePostconditionStrategy.isRemoveRule(app.rule())) {
				return true;
			} else {
				return false;
			}
			
		}
		



		@Override
		public Name name() {
			return RemovePostconditionStrategy.NAME;
		}

      @Override
      public boolean isStopAtFirstNonCloseableGoal() {
         return false;
      }
	}

	public String getName() {
		return "remove Postcondition (noninterference Proofs)";
	}

	@Override
	public String getCategory() {
		// TODO Auto-generated method stub
		
		return null;
	}

	@Override
	public String getDescription() {
		return "removes the postcondition for noninterference proofs";
	}

	@Override
	protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
		return new RemovePostconditionStrategy(proof
		        .getActiveStrategy());
	}

}
