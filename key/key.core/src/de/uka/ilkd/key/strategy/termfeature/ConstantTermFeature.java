package de.uka.ilkd.key.strategy.termfeature;

import org.key_project.common.core.logic.op.Function;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

public class ConstantTermFeature extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new ConstantTermFeature();
    
    private ConstantTermFeature() {
    }
    
    @Override
    protected boolean filter(Term term, Services services) {
        return term.op() instanceof Function && term.arity() == 0;
    }

}
