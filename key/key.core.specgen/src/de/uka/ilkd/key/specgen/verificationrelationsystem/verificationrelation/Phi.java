package de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation;

import de.uka.ilkd.key.logic.Term;

public class Phi {

	private Term myFormula;
	
	public Phi(Term formula) {
		myFormula = formula;
	}
	
	public Term getFormula() {
		return myFormula;
	}
	
}
