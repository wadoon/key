package de.uka.ilkd.key.gui.macros;

import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
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
    public String getDescription() {
        return "Continue atomatic rule application using abstract method calls and abstract class invariants.";
    }


    @Override
    protected Strategy createStrategy(KeYMediator mediator, PosInOccurrence posInOcc) {
        return new FinishAbstractProofStrategy(
                mediator.getInteractiveProver().getProof().getActiveStrategy());
    }

    @Override
    public KeyStroke getKeyStroke () {
	return KeyStroke.getKeyStroke(KeyEvent.VK_X, InputEvent.SHIFT_DOWN_MASK);
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
        	if (ruleApp instanceof TacletApp &&
        		(	((TacletApp)ruleApp).taclet().getRuleSets().contains(new RuleSet(new Name("expand_def"))) ||
        			((TacletApp)ruleApp).taclet().getRuleSets().contains(new RuleSet(new Name("classAxiom")))   ||
        			((TacletApp)ruleApp).taclet().getRuleSets().contains(new RuleSet(new Name("partialInvAxiom")))
        		)) {
        			return TopRuleAppCost.INSTANCE;
	        	}
        	else return delegate.computeCost(ruleApp, pio, goal);
        	
//            String name = ruleApp.rule().name().toString();
//            if(admittedRuleNames.contains(name)) {
//                return LongRuleAppCost.ZERO_COST;
//            } else {
//                return TopRuleAppCost.INSTANCE;
//            }
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            return delegate.isApprovedApp(app, pio, goal);
        }

        @Override
        public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                RuleAppCostCollector collector) {
        }

    }

}
