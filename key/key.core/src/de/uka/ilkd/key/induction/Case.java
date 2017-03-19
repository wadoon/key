package de.uka.ilkd.key.induction;

import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.op.Operator;

public class Case {

	private AbstractSortedOperator operator;	//specify this type of operator
	
	/**
	 * 
	 * @param op (logic.op.Operator) specifies the operator for the case
	 */
	public Case(AbstractSortedOperator op) {
		//TODO: check whether the sort of the given op is boolean
		this.operator = op;
	}

}
