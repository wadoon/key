package org.key_project.machlearning;


import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.GoalChooser;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;
import de.uka.ilkd.key.ui.ConsoleUserInterfaceControl;
import org.json.simple.JSONObject;

import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;
import java.util.Properties;
import java.util.Set;

public class FilterTactic implements Tactic {

    private static final Properties RULESET_MAP = computeRulesetMap();
    private final Set<String> rulesets;

    private static Properties computeRulesetMap() {
        Properties result = new Properties();
        InputStream resource = FilterTactic.class.getResourceAsStream("filterRulesets.xml");
        try {
            result.loadFromXML(resource);
        } catch (IOException e) {
            throw new ExceptionInInitializerError(e);
        }
        return result;
    }

    public static void registerTactics(Map<String, Tactic> tactics) {
        for (Object key : RULESET_MAP.keySet()) {
            String str = key.toString();
            tactics.put(str, new FilterTactic(str));
        }
    }

    public FilterTactic(String name) {
        rulesets = new HashSet<>(
                Arrays.asList(RULESET_MAP.getProperty(name).
                        trim().split("\\s*,\\s*")));
    }

    @Override
    public void apply(AbstractMediatorUserInterfaceControl ui, Proof proof, Goal goal, JSONObject command) throws Exception {

        Strategy oldStrategy = goal.getGoalStrategy();
        Strategy newStrategy = new FilterStrategy(oldStrategy);

        final GoalChooser goalChooser = proof.getInitConfig().getProfile().getSelectedGoalChooserBuilder().create();
        final ProverCore applyStrategy = new ApplyStrategy(goalChooser);
        proof.setActiveStrategy(newStrategy);
        try {
            applyStrategy.start(proof, goal);
        } finally {
            proof.setActiveStrategy(oldStrategy);
        }
    }


    private class FilterStrategy implements Strategy {

        private final Name NAME = new Name("Filter strategy");
        private final Strategy delegate;

        public FilterStrategy(Strategy delegate) {
            this.delegate = delegate;
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            return computeCost(app, pio, goal) != TopRuleAppCost.INSTANCE &&
                    // Assumptions are normally not considered by the cost
                    // computation, because they are normally not yet
                    // instantiated when the costs are computed. Because the
                    // application of a rule sometimes makes sense only if
                    // the assumptions are instantiated in a particular way
                    // (for instance equalities should not be applied on
                    // themselves), we need to give the delegate the possiblity
                    // to reject the application of a rule by calling
                    // isApprovedApp. Otherwise, in particular equalities may
                    // be applied on themselves.
                    delegate.isApprovedApp(app, pio, goal);
        }

        @Override
        public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {

            Rule rule = app.rule();
            if (rule instanceof Taclet) {
                Taclet taclet = (Taclet) rule;
                for (RuleSet ruleSet : taclet.getRuleSets()) {
                    if (rulesets.contains(ruleSet.name().toString())) {
                        return delegate.computeCost(app, pio, goal);
                    }
                }
                // System.err.println(taclet.getRuleSets() + " not in " + rulesets);
            }

            return TopRuleAppCost.INSTANCE;
        }

        @Override
        public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                                   RuleAppCostCollector collector) {
            delegate.instantiateApp(app, pio, goal, collector);
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }

    }



}
