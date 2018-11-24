package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.strategy.feature.MutableState;

public class ConstantTermFeature extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new ConstantTermFeature();
    
    private ConstantTermFeature() {
    }
    
    @Override
    protected boolean filter(Term term, Services services, MutableState mState) {
        return term.op() instanceof Function && term.arity() == 0;
    }

}
