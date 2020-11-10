package de.uka.ilkd.key.strategy.normalization;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.strategy.normalization.simple.SimpleFormulaNormalization;
import de.uka.ilkd.key.strategy.termfeature.BinaryTermFeature;

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
