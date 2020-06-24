package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.logic.*;
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

import java.util.ArrayList;
import java.util.List;

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

    public static List<String> forbiddenRuleSets = new ArrayList<>();
    public static List<String> forbiddenRules = new ArrayList<>();
    public static boolean firstOrderGoalsForbidden = false;

    static {
        // default rule sets and rules which may not be applied within an abstract proof
        forbiddenRuleSets.add("expand_def");
        forbiddenRuleSets.add("classAxiom");
        forbiddenRuleSets.add("partialInvAxiom");
    }

    private static boolean isInForbiddenRuleSet(RuleApp ruleApp, String ruleSetName) {
        return ((TacletApp)ruleApp).taclet().getRuleSets().contains(new RuleSet(new Name(ruleSetName)));
    }

    private static boolean isInForbiddenRuleSet(RuleApp ruleApp) {
        return forbiddenRuleSets.stream().anyMatch(ruleSetName -> isInForbiddenRuleSet(ruleApp, ruleSetName));
    }

    private static boolean isForbiddenRule(RuleApp ruleApp, String ruleName) {
        return ruleApp.rule().name().toString().equalsIgnoreCase(ruleName);
    }

    private static boolean isForbiddenRule(RuleApp ruleApp) {
        return forbiddenRules.stream().anyMatch(ruleName -> isForbiddenRule(ruleApp, ruleName));
    }
    
    private static class FinishAbstractProofStrategy implements Strategy {
    	
    	private final Strategy delegate;
        private static final Name NAME = new Name(FinishAbstractProofStrategy.class.getSimpleName());
        
        public FinishAbstractProofStrategy(Strategy delegate) {
            this.delegate = delegate;
        }

        /*
         * find a modality term in a node
         */
        private static boolean hasModality(Node node) {
            Sequent sequent = node.sequent();
            for (SequentFormula sequentFormula : sequent) {
                if(hasModality(sequentFormula.formula())) {
                    return true;
                }
            }

            return false;
        }

        /*
         * recursively descent into the term to detect a modality.
         */
        private static boolean hasModality(Term term) {
            if(term.op() instanceof Modality) {
                return true;
            }

            for (Term sub : term.subs()) {
                if(hasModality(sub)) {
                    return true;
                }
            }

            return false;
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public RuleAppCost computeCost(RuleApp ruleApp, PosInOccurrence pio, Goal goal) {
            if (ruleApp instanceof TacletApp &&
                    (isInForbiddenRuleSet(ruleApp) ||
                            (firstOrderGoalsForbidden && !hasModality(goal.node())) ||
                            isForbiddenRule(ruleApp)))
                return TopRuleAppCost.INSTANCE;
            else
                return delegate.computeCost(ruleApp, pio, goal);
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
