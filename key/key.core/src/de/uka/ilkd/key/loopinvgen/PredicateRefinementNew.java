package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.io.ProofSaver;

public class PredicateRefinementNew {

	public Set<Term> refinedCompList;
	public Set<Term> refinedDepList;

	private final Sequent seq;
	private Set<Term> allPredicates = new HashSet<>();
	private final Services services;
	private SideProof sProof;

	public PredicateRefinementNew(Services s, Sequent sequent, Set<Term> allPredList) {
		services = s;
		allPredicates = allPredList;
		seq = sequent;
		sProof = new SideProof(services, seq);
	}

	public Set<Term> predicateCheckAndRefine() {
		Set<Term> toDelete = new HashSet<>();
		for (Term pred : allPredicates) {
			if(!sequentImpliesPredicate(pred)) {
				toDelete.add(pred);
			}
		}
		allPredicates.removeAll(toDelete);
		return allPredicates;
	}

	
	private boolean sequentImpliesPredicate(Term pred) {
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(pred), false, true).sequent();
		for (SequentFormula sequentFormula : seq.antecedent()) {
			sideSeq=sideSeq.addFormula(sequentFormula, true, false).sequent();
		}

		for (SequentFormula sequentFormula : seq.succedent()) {
			if (!sequentFormula.formula().containsJavaBlockRecursive()) {
				sideSeq=sideSeq.addFormula(sequentFormula, false, false).sequent();
			}
		}
		
		final boolean provable = sProof.isProvable(sideSeq, services);
		if (!provable&& pred.op() == services.getTypeConverter().getDependenciesLDT().getNoR()) {
			System.out.println("NOT Proved: " + sideSeq);}
//		else if (provable && pred.op() == services.getTypeConverter().getDependenciesLDT().getNoR()) {
//			System.out.println("Check: " + ProofSaver.printAnything(sideSeq, services));
//		}
		return provable;
	}
}