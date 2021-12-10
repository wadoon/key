package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

public class IsGetterTermFeature implements TermFeature {

    public static final TermFeature INSTANCE = new IsGetterTermFeature();

    @Override
    public RuleAppCost compute(Term term, Services services) {
        Operator method = term.op();
        if(method.name().toString().contains("get")) {
            return NumberRuleAppCost.getZeroCost();
        }
        return TopRuleAppCost.INSTANCE;
    }
}
