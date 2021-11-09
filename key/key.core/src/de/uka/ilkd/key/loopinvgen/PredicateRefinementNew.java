package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.proof.io.ProofSaver;

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
	private final Term index;
	private final IntegerLDT intLDT;
	
	public PredicateRefinementNew(Services s, Sequent sequent, Set<Term> allPredList, Term i) {
		services = s;
		allPredicates = allPredList;
		seq = sequent;
		sProof = new SideProof(services, seq);
		depLDT = services.getTypeConverter().getDependenciesLDT();
		locsetLDT = services.getTypeConverter().getLocSetLDT();
		tb = services.getTermBuilder();
		index = i;
		intLDT = services.getTypeConverter().getIntegerLDT();
	}

	public Set<Term> predicateCheckAndRefine() {
		Set<Term> unProvenPreds = new HashSet<>();
		for (Term pred : allPredicates) {
//			System.out.println("Checking: " + pred);
			if (!sequentImpliesPredicate(pred)) {
//				checkedPredicates.add(pred);
				unProvenPreds.add(pred);
			}
		}
//		System.out.println("Size of predicate set: " + allPredicates.size());
		allPredicates.removeAll(unProvenPreds);
		Set<Term> weakenedPreds = new HashSet<>();
//		Set<Term> weakenedPredsChecked = new HashSet<>();
		for (Term un : unProvenPreds) {
			if (un.op() == depLDT.getNoR() || un.op() == depLDT.getNoW() || un.op() == depLDT.getNoRaW()
					|| un.op() == depLDT.getNoWaR() || un.op() == depLDT.getNoWaW()) {

				weakenedPreds.addAll(weakeningDependencePredicates(un));
//				for (Term t : weakenedPreds) {
//					if (!checkedPredicates.add(t))
//						weakenedPredsChecked.add(t);
//				}
			}
			else if(un.op() == intLDT.getLessThan() || un.op() == intLDT.getLessOrEquals() || un.op() == intLDT.getGreaterThan() || un.op() == intLDT.getGreaterOrEquals() || un.op() == Equality.EQUALS) {
				weakenedPreds.addAll(weakeningComparisonPredicates(un));
			} else
				System.out.println("Unknown Predicate");
		}
//		weakenedPreds.removeAll(weakenedPredsChecked);
		Set<Term> weakenedToDelete = new HashSet<>();
		for (Term weak : weakenedPreds) {
			if (!sequentImpliesPredicate(weak)) {
				weakenedToDelete.add(weak);
			}
		}
		weakenedPreds.removeAll(weakenedToDelete);
		allPredicates.addAll(weakenedPreds);
//		System.out.println("New Size of predicate set: " + allPredicates.size());
		System.out.println("Predicate Set After Refinement");
		for (Term term : allPredicates) {
			System.out.println(term);
		}
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
//		System.out.println("in: " +  sideSeq);
		final boolean provable = sProof.isProvable(sideSeq, services);
		if (!provable && pred.op() == services.getTypeConverter().getDependenciesLDT().getNoRaW()) {//
			System.out.println("NOT Proved: " + ProofSaver.printAnything(sideSeq, services));
		}
//		else if (provable && pred.op() == services.getTypeConverter().getDependenciesLDT().getNoR()) {
//			System.out.println("Check: " + ProofSaver.printAnything(sideSeq, services));
//		}
		return provable;
	}

	private Set<Term> weakeningDependencePredicates(Term unProven) {
		Set<Term> result = new HashSet<>();
		result.addAll(weakenByPredicateSymbol(unProven));
		result.addAll(weakenBySubSetANDPredicateSymbol(unProven));
		return result;
	}

	private Set<Term> weakenByPredicateSymbol(Term unProven) {
		Set<Term> result = new HashSet<>();
		if (unProven.sub(0) != locsetLDT.getEmpty()) {
			if (unProven.op().equals(depLDT.getNoR())) {
				result.add(tb.noRaW(unProven.sub(0)));
				result.add(tb.noWaR(unProven.sub(0)));
			} else if (unProven.op().equals(depLDT.getNoW())) {
				result.add(tb.noRaW(unProven.sub(0)));
				result.add(tb.noWaR(unProven.sub(0)));
				result.add(tb.noWaW(unProven.sub(0)));
			}
		}
		// TODO Also add weakening for the relaxed predicates
		return result;
	}

	private Set<Term> weakenBySubSetANDPredicateSymbol(Term unProven) {
		Set<Term> result = new HashSet<>();
		final Term locSet = unProven.sub(0);
		Term lowSingleton = null;
		Term highSingleton = null;
		Term subLoc = null;

//		Term opOnSubLocs = null;
		if (!locSet.equals(locsetLDT.getEmpty()) && locSet != null && locSet.op().equals(locsetLDT.getArrayRange())) {
			final Term array = locSet.sub(0);
			final Term low = locSet.sub(1);
			final Term newLow = tb.add(low, tb.one());
			final Term high = locSet.sub(2);
			final Term newHigh = tb.subtract(high, tb.one());
			
			if (lowLessThanHighPlusOne(low, high)) {
				subLoc = tb.arrayRange(array, newLow, newHigh);
				lowSingleton = tb.singleton(array, tb.arr(low));
				highSingleton = tb.singleton(array, tb.arr(high));
				
				if (unProven.op().equals(depLDT.getNoR())) {
					result.add(tb.noR(subLoc));
					result.add(tb.noR(lowSingleton));
					result.add(tb.noR(highSingleton));
					result.add(tb.noRaW(subLoc));
					result.add(tb.noRaW(lowSingleton));
					result.add(tb.noRaW(highSingleton));
					result.add(tb.noWaR(subLoc));
					result.add(tb.noWaR(lowSingleton));
					result.add(tb.noWaR(highSingleton));
				} else if (unProven.op().equals(depLDT.getNoW())) {
					result.add(tb.noW(subLoc));
					result.add(tb.noW(lowSingleton));
					result.add(tb.noW(highSingleton));
					result.add(tb.noRaW(subLoc));
					result.add(tb.noRaW(lowSingleton));
					result.add(tb.noRaW(highSingleton));
					result.add(tb.noWaR(subLoc));
					result.add(tb.noWaR(lowSingleton));
					result.add(tb.noWaR(highSingleton));
					result.add(tb.noWaW(subLoc));
					result.add(tb.noWaW(lowSingleton));
					result.add(tb.noWaW(highSingleton));
					
				} else if (unProven.op().equals(depLDT.getNoRaW())) {
					result.add(tb.noRaW(subLoc));
					result.add(tb.noRaW(lowSingleton));
					result.add(tb.noRaW(highSingleton));
				} else if (unProven.op().equals(depLDT.getNoWaR())) {
					result.add(tb.noWaR(subLoc));
					result.add(tb.noWaR(lowSingleton));
					result.add(tb.noWaR(highSingleton));
				} else if (unProven.op().equals(depLDT.getNoWaW())) {
					result.add(tb.noWaW(subLoc));
					result.add(tb.noWaW(lowSingleton));
					result.add(tb.noWaW(highSingleton));
				}
			}
		}
		// TODO Also add weakening for the relaxed predicates
		return result;
	}
	private boolean lowLessThanHighPlusOne(Term low, Term high) {
		Term comparison = tb.lt(low, tb.add(high,tb.one()));
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(comparison), false, true).sequent();
		for (SequentFormula sequentFormula : seq.antecedent()) {
			sideSeq = sideSeq.addFormula(sequentFormula, true, false).sequent();
		}

		for (SequentFormula sequentFormula : seq.succedent()) {
			if (!sequentFormula.formula().containsJavaBlockRecursive()) {
				sideSeq = sideSeq.addFormula(sequentFormula, false, false).sequent();
			}
		}
		return sProof.isProvable(sideSeq, services);
	}
	
	private Set<Term> weakeningComparisonPredicates(Term pred) {
		Set<Term> result = new HashSet<>();
		Term low = pred.sub(0);
		Term high = pred.sub(1);
		if(low != null && high!= null) {
			if(pred.op()== intLDT.getLessThan()) {
				result.add(tb.leq(low, high));
				result.add(tb.geq(high, low));
			} else if(pred.op() == intLDT.getGreaterThan()) {
				result.add(tb.geq(low, high));
				result.add(tb.leq(high, low));
			} else if(pred.op() == Equality.EQUALS) {
				result.add(tb.geq(low, high));
				result.add(tb.leq(low, high));
			}
		}
		
		return result;
	}
}