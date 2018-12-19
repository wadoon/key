package de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation;

import de.uka.ilkd.key.logic.Term;

public class Delta {

	private Term myUpdate;
	
	public Delta(Term update) {
		myUpdate = update;
	}
	
	public Term getUpdate() {
		return myUpdate;
	}
	
}
