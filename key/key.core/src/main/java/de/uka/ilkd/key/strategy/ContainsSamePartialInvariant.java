package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.BinaryFeature;
import de.uka.ilkd.key.strategy.feature.Feature;

public class ContainsSamePartialInvariant extends BinaryFeature {

	final static Feature ANTEC_INSTANCE = new ContainsSamePartialInvariant(true);
    final static Feature SUCC_INSTANCE = new ContainsSamePartialInvariant(false);
	private final boolean findInAntec;

	private ContainsSamePartialInvariant(boolean findInAntec) {
		this.findInAntec = findInAntec;
	}

	@Override
	protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
	    Operator findOp = pos.subTerm().op();
	    
	    final Services services = goal.proof().getServices();
	    final IObserverFunction inv = services.getJavaInfo().getInv();
	    
	    for (SequentFormula sf : findInAntec ? goal.sequent().succedent() : goal.sequent().antecedent()) {
	    	OpCollector collector = new OpCollector();
	    	sf.formula().execPostOrder(collector);
	    	if (collector.contains(findOp)|| collector.contains(inv)) return true;
	    }
		return false;
	}

}
