package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (23.11.17)
 */
public class StrategyCostChanger implements Strategy {
    private final Strategy other;
    private final Map<String, RuleAppCost> forbiddenTaclets = new HashMap<>();
    private final Map<String, RuleAppCost> forbiddenRuleSets = new HashMap<>();
    private boolean allowOneStepSimplifier = true;

    public StrategyCostChanger(Strategy other) {
        this.other = other;
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return other.isStopAtFirstNonCloseableGoal();
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return other.isApprovedApp(app, pio, goal);
    }

    @Override
    public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal, RuleAppCostCollector collector) {
        other.instantiateApp(app, pio, goal, collector);
    }

    @Override
    public Name name() {
        return new Name(other.name().toString() + "*");
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        RuleAppCost cost = other.computeCost(app, pos, goal);
        String name = app.rule().name().toString();
        if (forbiddenTaclets.containsKey(name)) {
            return forbiddenTaclets.get(name).add(cost);
        }


        return cost;
    }

    public static class Builder {
        private StrategyCostChanger instance = new StrategyCostChanger(other);

        /**
         * @param name comma-separated
         * @return
         */
        public Builder forbidTaclets(String name) {
            return forbidTaclets(name.split(","));
        }

        public Builder forbidTaclets(String... name) {
            Arrays.stream(name).forEachOrdered(this::forbidTaclet);
            return this;
        }

        public Builder forbidTaclet(String name) {
            instance.forbiddenTaclets.add(name);
            return this;
        }

        public Builder forbidTaclet(Taclet tac) {
            return forbidTaclet(tac.name());
        }

        public Builder forbidTaclet(Name name) {
            return forbidTaclet(name.toString());
        }

        public Builder forbidRuleset(Name name) {
            return forbidRuleset(name.toString());
        }

        public Builder allowTaclet(String tacletName) {
            //TODO
            return this;
        }

        public Builder changeCost(double factor, String tacletNames)

        /**
         * Removes '@'
         *
         * @param set
         * @return
         */
        public Builder forbidRuleset(String set) {
            instance.forbiddenRuleSets.add(set.replace("@", ""));
            return this;
        }

        public Builder allowOneStepSimplification() {
            return allowOneStepSimplification(true);
        }

        public Builder allowOneStepSimplification(boolean allow) {
            instance.allowOneStepSimplifier = allow;
            return this;
        }

        public StrategyCostChanger build() {
            return instance;
        }
    }
}
