package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;

import java.util.List;

/**
 * Binary feature that returns zero iff a certain Taclet app has not already been performed
 */
public class NonDuplicateAppFeature extends AbstractNonDuplicateAppFeature {

    public static final Feature INSTANCE = new NonDuplicateAppFeature();

    protected boolean ruleAppIsAbsent(Goal goal, TacletApp rapp,
            PosInOccurrence pio) {
        List<RuleApp> apps = getRuleAppsWithName(goal.node(), rapp.rule().name());
        if (apps != null) {
            for (RuleApp a : apps) {
                if (sameApplication(a, rapp, pio))
                    return false;
            }
        }

        return true;
    }

    public boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        if (!app.ifInstsComplete()) {
            return true;
        }

        if (pos == null) {
            return ruleAppIsAbsent(goal, app, pos);
        }

        return noDuplicateFindTaclet(app, pos, goal);
    }

    protected boolean comparePio(TacletApp newApp, TacletApp oldApp, PosInOccurrence newPio,
            PosInOccurrence oldPio) {
        return oldPio.equals(newPio);
    }

    protected boolean semiSequentContains(Semisequent semisequent, SequentFormula cfma) {
        return semisequent.contains(cfma);
    }
}
