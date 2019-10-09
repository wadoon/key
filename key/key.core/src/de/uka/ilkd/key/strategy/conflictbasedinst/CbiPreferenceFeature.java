package de.uka.ilkd.key.strategy.conflictbasedinst;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.BinaryFeature;

public class CbiPreferenceFeature extends BinaryFeature {

    private CbiPreferenceFeature() {}

    public static final CbiPreferenceFeature INSTANCE = new CbiPreferenceFeature();

    @Override
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        boolean solved = CbiProjection.getInstance().solved(app, pos, goal);
        return !solved;
    }



}
