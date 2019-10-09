package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

public class ContainsPartialInvariantTwice extends BinaryFeature {

	@Override
	protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
	    Operator findOp = pos.subTerm().op();
	    
	    int encountered = 0;
	    for (SequentFormula sf : goal.sequent().antecedent()) {
	    	OpCollector collector = new OpCollector();
	    	//collector.visit(sf.formula());
	    	sf.formula().execPreOrder(collector);
	    	if (collector.contains(findOp)) encountered++;
	    }
		if(encountered > 1) {
			return true;
		} else {
			return false;
		}
	}

}
