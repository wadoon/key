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

    /**
     *
     */
    protected Map<String, Long> factorForRuleNames = new HashMap<>();


    /**
     * @param delegate
     */
    protected Map<String, Long> factorForRulesets = new HashMap<>();


    /**
     *
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
        // if new cost is zero, then return immediately
        String ruleName = app.rule().name().toString();
        if (factorForRuleNames.getOrDefault(ruleName, -1L) == 0D) {
            return NumberRuleAppCost.getZeroCost();
        }

        RuleAppCost defaultCost = delegate.computeCost(app, pos, goal);
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
        }
    }


    public Long ruleSetFactor(RuleApp app) {
        try {
            Taclet t = (Taclet) app.rule();
            for (RuleSet rs : t.getRuleSets()) {
                String name = rs.name().toString();
                if (factorForRulesets.containsKey(name)) {
                    return factorForRulesets.get(name);
                }
            }
        } catch (ClassCastException e) {
        }
        return 1L;
    }
}
