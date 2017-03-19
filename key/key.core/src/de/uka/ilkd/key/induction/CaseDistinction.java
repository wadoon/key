package de.uka.ilkd.key.induction;

import java.util.LinkedList;

import de.uka.ilkd.key.logic.op.QuantifiableVariable;

public class CaseDistinction {

	private QuantifiableVariable variable;
	private LinkedList<Case> cases;
	
	public CaseDistinction(QuantifiableVariable v, LinkedList<Case> c) {
		this.variable = v;
	}

}
