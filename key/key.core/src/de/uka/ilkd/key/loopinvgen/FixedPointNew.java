package de.uka.ilkd.key.loopinvgen;

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;

public class FixedPointNew {
	private Services s;
	private Sequent seq;
	private Set<Term> preds;
	private SideProof sp;

	public FixedPointNew(Services services, Sequent sequent, Set<Term> predicates) {
		s = services;
		seq = sequent;
		preds = predicates;
		sp = new SideProof(s, seq);
	}

	public boolean reachedFixedPoint() {
		for (SequentFormula sf : seq) {
			if (!sf.formula().containsJavaBlockRecursive()) {
				if (!predicatesImplyFormula(sf)) {
					return false;
				}
			}
		}
		return true;
	}

	
	private boolean predicatesImplyFormula(SequentFormula formula) {
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(formula, false, true).sequent();
		for (Term p : preds) {
			sideSeq = sideSeq.addFormula(new SequentFormula(p), true, true).sequent();
		}
//		System.out.println("To prove: " + sideSeq);
		return sp.isProvable(sideSeq, s);

	}
}
