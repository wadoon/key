package de.uka.ilkd.key.loopinvgen;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.util.ProgressMonitor.Empty;

public class PredicateRefinementNew {

	public Set<Term> refinedCompList;
	public Set<Term> refinedDepList;

	private final Sequent seq;
	private Set<Term> allPredicates = new HashSet<>();
	private Set<Term> checkedPredicates = new HashSet<>();
	private final Services services;
	private SideProof sProof;
	private final DependenciesLDT depLDT;
	private final LocSetLDT locsetLDT;
	private final TermBuilder tb;

	public PredicateRefinementNew(Services s, Sequent sequent, Set<Term> allPredList) {
		services = s;
		allPredicates = allPredList;
		seq = sequent;
		sProof = new SideProof(services, seq);
		depLDT = services.getTypeConverter().getDependenciesLDT();
		locsetLDT = services.getTypeConverter().getLocSetLDT();
		tb = services.getTermBuilder();
	}

	public Set<Term> predicateCheckAndRefine() {
		Set<Term> unProvenPreds = new HashSet<>();
		for (Term pred : allPredicates) {
			System.out.println("Checking: " + pred);
			if (!sequentImpliesPredicate(pred)) {
				checkedPredicates.add(pred);
				unProvenPreds.add(pred);
			}
		}
//		System.out.println("Size of predicate set: " + allPredicates.size());
		allPredicates.removeAll(unProvenPreds);
//		Set<Term> weakenedPreds = new HashSet<>();
//		Set<Term> weakenedPredsChecked = new HashSet<>();
//		for (Term un : unProvenPreds) {
//			if (un.op() == depLDT.getNoR() || un.op() == depLDT.getNoW() || un.op() == depLDT.getNoRaW()
//					|| un.op() == depLDT.getNoWaR() || un.op() == depLDT.getNoWaW()) {
//			
//				weakenedPreds.addAll(weakeningPredicates(un));
//				for(Term t : weakenedPreds){
//					if(!checkedPredicates.add(t))
//						weakenedPredsChecked.add(t);		
//				}
//			}
//		}
//		weakenedPreds.removeAll(weakenedPredsChecked);		
//		allPredicates.addAll(weakenedPreds);
//		System.out.println("New Size of predicate set: " + allPredicates.size());
		return allPredicates;
	}

	private boolean sequentImpliesPredicate(Term pred) {
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(pred), false, true).sequent();
		for (SequentFormula sequentFormula : seq.antecedent()) {
			sideSeq = sideSeq.addFormula(sequentFormula, true, false).sequent();
		}

		for (SequentFormula sequentFormula : seq.succedent()) {
			if (!sequentFormula.formula().containsJavaBlockRecursive()) {
				sideSeq = sideSeq.addFormula(sequentFormula, false, false).sequent();
			}
		}
		final boolean provable = sProof.isProvable(sideSeq, services);
		if (!provable && pred.op() == services.getTypeConverter().getDependenciesLDT().getNoWaW()) {// SEE THE OUTPUT ON MONDAY
			System.out.println("NOT Proved in " + sideSeq);
		}
//		else if (provable && pred.op() == services.getTypeConverter().getDependenciesLDT().getNoR()) {
//			System.out.println("Check: " + ProofSaver.printAnything(sideSeq, services));
//		}
		return provable;
	}

	private Set<Term> weakeningPredicates(Term unProven) {
		Set<Term> result = new HashSet<>();
		result.addAll(weakenByPredicateSymbol(unProven));
		result.addAll(weakenBySubSet(unProven));
		return result;
	}

	private Set<Term> weakenByPredicateSymbol(Term unProven) {
		Set<Term> result = new HashSet<>();
		if (unProven.op().equals(depLDT.getNoR())) {
			System.out.println("Weakening " + unProven);
			result.add(tb.noRaW(unProven.sub(0)));
			result.add(tb.noWaR(unProven.sub(0)));
		} else if (unProven.op().equals(depLDT.getNoW())) {
			result.add(tb.noRaW(unProven.sub(0)));
			result.add(tb.noWaR(unProven.sub(0)));
			result.add(tb.noWaW(unProven.sub(0)));
		}
//		else if(unProven.op().equals(depLDT.getNoRaW()) || unProven.op().equals(depLDT.getNoWaR()) || unProven.op().equals(depLDT.getNoWaW())) {//how necessery is this case?
//			result.add(tb.tt());
//		}

		// TODO Also add weakening for the relaxed predicates
		return result;
	}

	private Set<Term> weakenBySubSet(Term unProven) {
		Set<Term> result = new HashSet<>();
		Term locSet = unProven.sub(0);
		Term subLoc1 = null;
		Term subLoc2 = null;
		Term opOnSubLocs = null;
		if (!locSet.equals(locsetLDT.getEmpty()) && locSet != null && locSet.op().equals(locsetLDT.getArrayRange())) {
			if (sProof.proofLT(locSet.sub(1), locSet.sub(2))) { // l < h
				subLoc1 = tb.arrayRange(locSet.sub(0), locSet.sub(1), tb.subtract(locSet.sub(2), tb.one()));// arrayRange(arr,l,h-1)
				subLoc2 = tb.arrayRange(locSet.sub(0), tb.subtract(locSet.sub(1), tb.one()), locSet.sub(2));// arrayRange(arr,l-1,h)
			}
			if (unProven.op().equals(depLDT.getNoR())) {
				result.add(tb.noR(subLoc1));
				result.add(tb.noR(subLoc2));
			} else if (unProven.op().equals(depLDT.getNoW())) {
				result.add(tb.noW(subLoc1));
				result.add(tb.noW(subLoc2));
			} else if (unProven.op().equals(depLDT.getNoRaW())) {
				result.add(tb.noRaW(subLoc1));
				result.add(tb.noRaW(subLoc2));
			} else if (unProven.op().equals(depLDT.getNoWaR())) {
				result.add(tb.noWaR(subLoc1));
				result.add(tb.noWaR(subLoc2));
			} else if (unProven.op().equals(depLDT.getNoWaW())) {
				result.add(tb.noWaW(subLoc1));
				result.add(tb.noWaW(subLoc2));
			}
		}
		// TODO Also add weakening for the relaxed predicates
		return result;
	}
}