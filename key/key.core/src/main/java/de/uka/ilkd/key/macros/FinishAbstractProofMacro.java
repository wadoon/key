package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

public class FinishAbstractProofMacro extends StrategyProofMacro {
	@Override
    public String getName() {
        return "Finish abstract proof part";
    }

    @Override
    public String getCategory() {
        return null;
    }

    @Override
    public String getDescription() {
        return "Continue atomatic rule application using abstract method calls and abstract class invariants.";
    }

    @Override
    protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        return new FinishAbstractProofStrategy(proof.getActiveStrategy());
    }
    
    private static class FinishAbstractProofStrategy implements Strategy {
    	
    	private final Strategy delegate;
        private static final Name NAME = new Name(FinishAbstractProofStrategy.class.getSimpleName());
        
        public FinishAbstractProofStrategy(Strategy delegate) {
            this.delegate = delegate;
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public RuleAppCost computeCost(RuleApp ruleApp, PosInOccurrence pio, Goal goal) {
            // TODO: review optimization strategy in b26e24d9c54379533b988dbbee41cb51b08055fa
            if (ruleApp instanceof TacletApp &&
                    (	((TacletApp)ruleApp).taclet().getRuleSets().contains(new RuleSet(new Name("expand_def"))) ||
                        ((TacletApp)ruleApp).taclet().getRuleSets().contains(new RuleSet(new Name("classAxiom")))   ||
                        ((TacletApp)ruleApp).taclet().getRuleSets().contains(new RuleSet(new Name("partialInvAxiom")))
                    )) {
                    return TopRuleAppCost.INSTANCE;
                    }
            else {
                return delegate.computeCost(ruleApp, pio, goal);
            }
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            return delegate.isApprovedApp(app, pio, goal);
        }

        @Override
        public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                RuleAppCostCollector collector) {
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }
    }

}
