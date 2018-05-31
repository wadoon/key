package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * @author Alexander Weigl
 * @version 1 (30.05.18)
 */
public class AdaptableStrategy implements Strategy {
    /**
     *
     */
    protected final Strategy delegate;

    /**
     *
     */
    protected Set<String> disabledRulesByName = new HashSet<>();

    protected CostAdapter costAdapter = new NeutralCostAdapter();

    /**
     * @param delegate
     */
    public AdaptableStrategy(Strategy delegate) {
        this.delegate = delegate;
    }

    /**
     * @return
     */
    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return delegate.isStopAtFirstNonCloseableGoal();
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        if (disabledRulesByName.contains(app.rule().name().toString())) {
            return false;
        }
        return delegate.isApprovedApp(app, pio, goal);
    }

    @Override
    public void instantiateApp(RuleApp app, PosInOccurrence pio,
                               Goal goal, RuleAppCostCollector collector) {
        delegate.instantiateApp(app, pio, goal, collector);
    }

    @Override
    public Name name() {
        return new Name(getClass().getSimpleName());
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        /*// if new cost is zero, then return immediately
        String ruleName = app.rule().name().toString();
        if (factorForRuleNames.getOrDefault(ruleName, -1L) == 0D) {
            return NumberRuleAppCost.getZeroCost();
        }

        long rSF = ruleSetFactor(app);
        if (rSF == 0) {
            return NumberRuleAppCost.getZeroCost();
        } else if (rSF != 1) {
            defaultCost = defaultCost.mul(NumberRuleAppCost.create(rSF));
        }

        if (!factorForRuleNames.containsKey(ruleName)) {
            return defaultCost;
        } else {
            NumberRuleAppCost factorCost = (NumberRuleAppCost) NumberRuleAppCost.create(factorForRuleNames.get(ruleName));
            return factorCost.mul(defaultCost);
        }*/
        RuleAppCost defaultCost = delegate.computeCost(app, pos, goal);
        return costAdapter.computeCost(defaultCost, app, pos, goal);
    }

    interface CostAdapter {
        public RuleAppCost computeCost(RuleAppCost oldCost, RuleApp app,
                                       PosInOccurrence pos, Goal goal);
    }

    public static class SetBasedCostAdapter<T> extends LinearCostAdapater {
        protected Map<T, Long> summandMap = new HashMap<>();
        protected Map<T, Long> factorMap = new HashMap<>();
        protected Function<RuleApp, T> translateApp;

        public SetBasedCostAdapter(Function<RuleApp, T> translate) {
            this.translateApp = translate;

            Function<RuleApp, RuleAppCost> summandNeutral = summand;
            Function<RuleApp, RuleAppCost> factorNeutral = factor;

            this.summand = (RuleApp app) -> {
                T key = this.translateApp.apply(app);
                if (summandMap.containsKey(key)) {
                    return NumberRuleAppCost.create(summandMap.get(key));
                }
                return summandNeutral.apply(app);
            };

            this.factor = (RuleApp app) -> {
                T key = this.translateApp.apply(app);
                if (factorMap.containsKey(key)) {
                    return NumberRuleAppCost.create(factorMap.get(key));
                }
                return factorNeutral.apply(app);
            };
        }
    }

    public static class RuleNameAndSetAdapter implements CostAdapter {
        SetBasedCostAdapter<String> ruleSet = new SetBasedCostAdapter<>(app -> "");
        SetBasedCostAdapter<String> ruleName = new SetBasedCostAdapter<>(
                (app) -> app.rule().name().toString());

        public RuleNameAndSetAdapter() {
            ruleSet.translateApp = (app) -> {
                try {
                    Taclet t = (Taclet) app.rule();
                    for (RuleSet rs : t.getRuleSets()) {
                        String name = rs.name().toString();
                        if (ruleSet.factorMap.containsKey(name)) {
                            return name;
                        }
                    }
                } catch (ClassCastException e) {
                }
                return null;
            };
        }

        @Override
        public RuleAppCost computeCost(RuleAppCost oldCost, RuleApp app, PosInOccurrence pos, Goal goal) {
            return ruleName.computeCost(ruleSet.computeCost(oldCost, app, pos, goal), app, pos, goal);
        }
    }

    public abstract static class LinearCostAdapater implements CostAdapter {
        protected java.util.function.Function<RuleApp, RuleAppCost> summand = (app) -> NumberRuleAppCost.getZeroCost();
        protected java.util.function.Function<RuleApp, RuleAppCost> factor = (app) -> NumberRuleAppCost.create(1);

        @Override
        public RuleAppCost computeCost(RuleAppCost oldCost, RuleApp app, PosInOccurrence pos, Goal goal) {
            return oldCost.mul(factor.apply(app)).add(summand.apply(app));
        }
    }

    private static class NeutralCostAdapter implements CostAdapter {
        @Override
        public RuleAppCost computeCost(RuleAppCost oldCost, RuleApp app, PosInOccurrence pos, Goal goal) {
            return oldCost;
        }
    }
}
