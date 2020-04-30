package de.uka.ilkd.key.strategy.normalization;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.feature.BinaryFeature;
import de.uka.ilkd.key.strategy.termfeature.BinaryTermFeature;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

public class NormalizedAllFeature extends BinaryTermFeature {

    private static NormalizedAllFeature instance = new NormalizedAllFeature();

    public static NormalizedAllFeature getInstance() {
        return instance;
    }

    @Override
    protected boolean filter(Term term, Services services) {

        SimpleFormulaNormalization sfp = new SimpleFormulaNormalization(services.getTermBuilder(),
                services.getTermFactory(), false, false);
        Term normalized = sfp.getNormalized(term);
        boolean ret = term.op() == Quantifier.ALL;
        if(ret) {
            //System.out.println("Is All: " + term);
        }else {
            System.out.println("IS NOT ALL !!!!!!! " + term);
        }
        return ret;
    }
}
