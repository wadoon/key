package de.uka.ilkd.key.specgen.generator;

import de.uka.ilkd.key.logic.Term;

public class Invariant implements SpecGenResult {

	private Term myFormula;
	
	public Invariant(Term formula) {
		myFormula = formula;
	}
	
	public Term getFormula() {
		return myFormula;
	}
	
}
