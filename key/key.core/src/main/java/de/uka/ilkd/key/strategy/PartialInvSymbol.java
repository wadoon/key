package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

public class PartialInvSymbol implements TermFeature {

	public static TermFeature INSTANCE = new PartialInvSymbol();
	
	@Override
	public RuleAppCost compute(Term term, Services services) {
		return term.op() instanceof IObserverFunction && term.op().name().toString().contains("<p_inv") ? 
				NumberRuleAppCost.getZeroCost() : TopRuleAppCost.INSTANCE;
	}

}
