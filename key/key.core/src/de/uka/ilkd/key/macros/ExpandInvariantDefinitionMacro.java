package de.uka.ilkd.key.macros;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.Strategy;

public class ExpandInvariantDefinitionMacro extends StrategyProofMacro  {

    @Override
    public String getName() {
        return "Expand definitions";
    }

    @Override
    public String getCategory() {
        return "Auto Pilot";
    }

    @Override
    public String getDescription() {
        return "Expand invariant and other observer function definitions";
    }

    @Override
    protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        return new ExpandStrategy(proof.getActiveStrategy());
    }

    /*
     * convert a string array to a set of strings
     */
    protected static <E> Set<E> asSet(E... strings) {
        return Collections.unmodifiableSet(new LinkedHashSet<E>(Arrays.asList(strings)));
    }

    private static class ExpandStrategy extends FilterStrategy {

        private static final String[] PREFIXES =
                { "Class_invariant_axiom_" };

        public ExpandStrategy(Strategy delegate) {
            super(delegate);
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }

        @Override
        public Name name() {
            return new Name("Expand definitions strategy");
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {

            String name = app.rule().name().toString();
            for (String prefix : PREFIXES) {
                if(name.startsWith(prefix)) {
                    return super.isApprovedApp(app, pio, goal);
                }
            }

            if(app.rule() instanceof OneStepSimplifier) {
                Term term = pio.subTerm();
                while(term.op() == UpdateApplication.UPDATE_APPLICATION) {
                    term = term.sub(0);
                }

                // XXX Better matching here
                if(term.op() instanceof ObserverFunction) {
                    return super.isApprovedApp(app, pio, goal);
                }
            }

            return false;

        }

    }

}
