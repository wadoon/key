package de.uka.ilkd.key.strategy.conflictbasedinst;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.feature.Feature;

public class CbiPreferenceFeature implements Feature{

    private Feature feature;

    public CbiPreferenceFeature(Feature feature) {
        this.feature = feature;
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos,
            Goal goal) {
        if(ConflictBasedInstantiationOld.getInstance().solved(pos, goal)) {
            return TopRuleAppCost.INSTANCE;
        }
        return feature.computeCost(app, pos, goal);
    }

    public static Feature create(Feature feature) {
        return new CbiPreferenceFeature(feature);
    }

}
