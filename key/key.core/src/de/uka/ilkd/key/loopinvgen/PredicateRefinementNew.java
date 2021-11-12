package de.uka.ilkd.key.loopinvgen;

import java.util.Collection;
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
import de.uka.ilkd.key.logic.op.Operator;
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
	private final int itrNumber;

	public PredicateRefinementNew(Services s, Sequent sequent, Set<Term> allPredList, Term i, int itr) {
		services = s;
		allPredicates = allPredList;
		seq = sequent;
		sProof = new SideProof(services, seq);
		depLDT = services.getTypeConverter().getDependenciesLDT();
		locsetLDT = services.getTypeConverter().getLocSetLDT();
		tb = services.getTermBuilder();
		index = i;
//		System.out.println(index);
		intLDT = services.getTypeConverter().getIntegerLDT();
		itrNumber = itr;
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
			} else if (un.op() == intLDT.getLessThan() || un.op() == intLDT.getLessOrEquals()
					|| un.op() == intLDT.getGreaterThan() || un.op() == intLDT.getGreaterOrEquals()
					|| un.op() == Equality.EQUALS) {
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
//		System.out.println("Predicate Set After Refinement");
//		for (Term term : allPredicates) {
//			System.out.println(term);
//		}
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
//		if (!provable && pred.op() == services.getTypeConverter().getDependenciesLDT().getNoRaW()) {//
//			System.out.println("NOT Proved: " + ProofSaver.printAnything(sideSeq, services));
//		}
//		else if (provable && pred.op() == services.getTypeConverter().getDependenciesLDT().getNoR()) {
//			System.out.println("Check: " + ProofSaver.printAnything(sideSeq, services));
//		}
		return provable;
	}

	private Set<Term> weakeningDependencePredicates(Term unProven) {
		Set<Term> result = new HashSet<>();
		System.out.println("for " + unProven + " weaken by ");
//		System.out.println("predicate symbol added: ");
		result.addAll(weakenByPredicateSymbol(unProven));// 0, 2, or 3
//		System.out.println("index added: ");
		result.addAll(weakenByIndex(unProven));// 0 or 2
//		System.out.println("subset added: ");
//		if (itrNumber < 2)
//			result.addAll(weakenBySubSet(unProven)); // 0 or 3
		System.out.println("sequent added: ");
		result.addAll(weakenBySequent(unProven)); // 0 or 1
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
//		System.out.println(result);
		return result;
	}

	private Set<Term> weakenBySubSet(Term unProven) {
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
			if (sProof.proofLT(low, high)) {
				lowSingleton = tb.singleton(array, tb.arr(low));
				highSingleton = tb.singleton(array, tb.arr(high));
				if (!sProof.proofEquality(newLow, newHigh))
					subLoc = tb.arrayRange(array, newLow, newHigh);
				else
					subLoc = tb.singleton(array, tb.arr(newLow));

				if (unProven.op().equals(depLDT.getNoR())) {
					result.add(tb.noR(subLoc));
					result.add(tb.noR(lowSingleton));
					result.add(tb.noR(highSingleton));
				} else if (unProven.op().equals(depLDT.getNoW())) {
					result.add(tb.noW(subLoc));
					result.add(tb.noW(lowSingleton));
					result.add(tb.noW(highSingleton));
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
//		System.out.println(result);
		return result;
	}

	private Set<Term> weakenBySequent(Term unProven) {
		Operator Pred = unProven.op();
		Term locSet = unProven.sub(0);
		Set<Term> result = new HashSet<>();
//		System.out.println("for " + unProven + " weaken by sequent added: ");
		for (SequentFormula sequentFormula1 : seq.antecedent()) {
			Term seqLocSet1 = sequentFormula1.formula().sub(0);
			if (sequentFormula1.formula().op() == depLDT.getRPred()) {
//				if (Pred == depLDT.getNoR() && sProof.proofNonEmptyIntersection(locSet, seqLocSet1)) {
//					result.add(tb.noR(tb.setMinus(locSet, seqLocSet1)));
//				} else
				if (Pred == depLDT.getNoRaW() && sProof.proofNonEmptyIntersection(locSet, seqLocSet1)) {
					for (SequentFormula sequentFormula2 : seq.antecedent()) {
						Term seqLocSet2 = sequentFormula2.formula().sub(0);
						if (sequentFormula2.formula().op() == depLDT.getWPred()
								&& sProof.proofNonEmptyIntersection(tb.intersect(locSet, seqLocSet1), seqLocSet2)) {
							Term seqLabel1 = sequentFormula1.formula().sub(1);
							Term seqLabel2 = sequentFormula2.formula().sub(1);
							if (sProof.proofLT(seqLabel2, seqLabel1)) {
								result.add(tb.noRaW(tb.setMinus(locSet, tb.intersect(seqLocSet1, seqLocSet2))));
//								System.out.println("because "+ seqLabel2 + " is less then " + " there is a " + sequentFormula1 + " after "+ sequentFormula2);
							} 
						}
					}
				} else if (Pred == depLDT.getNoWaR() && sProof.proofNonEmptyIntersection(locSet, seqLocSet1)) {
					for (SequentFormula sequentFormula2 : seq.antecedent()) {
						Term seqLocSet2 = sequentFormula2.formula().sub(0);
						if (sequentFormula2.formula().op() == depLDT.getWPred()
								&& sProof.proofNonEmptyIntersection(tb.intersect(locSet, seqLocSet1), seqLocSet2)) {
							Term seqLabel1 = sequentFormula1.formula().sub(1);
							Term seqLabel2 = sequentFormula2.formula().sub(1);
							if (sProof.proofLT(seqLabel1, seqLabel2)) {
								result.add(tb.noWaR(tb.setMinus(locSet, tb.intersect(seqLocSet1, seqLocSet2))));
							}
						}
					}
				}
			} else if (sequentFormula1.formula().op() == depLDT.getWPred()) {
				if (sProof.proofNonEmptyIntersection(locSet, seqLocSet1)) {
					if (Pred == depLDT.getNoW()) {
						result.add(tb.noW(tb.setMinus(locSet, seqLocSet1)));
					} else if (Pred == depLDT.getNoWaW()) {
						for (SequentFormula sequentFormula2 : seq.antecedent()) {
							Term seqLocSet2 = sequentFormula2.formula().sub(0);
							if (sequentFormula2.formula().op() == depLDT.getWPred()
									&& sProof.proofNonEmptyIntersection(tb.intersect(locSet, seqLocSet1), seqLocSet2)) {
								Term seqLabel1 = sequentFormula1.formula().sub(1);
								Term seqLabel2 = sequentFormula2.formula().sub(1);
								if (!sProof.proofEquality(seqLabel1, seqLabel2)) {
									result.add(tb.noWaW(tb.setMinus(locSet, tb.intersect(seqLocSet1, seqLocSet2))));
								}
							}
						}
					}
				}

			}
		}
//		System.out.println(result);
		return result;
	}

	private Term findArrayRange(Term locSet) {
		if(locSet.op()==locsetLDT.getArrayRange()) {
			
			return locSet;
		}
//		else if(locSet.op()==locsetLDT.getUnion() || locSet.op()==locsetLDT.getIntersect() || locSet.op()==locsetLDT.getSetMinus()) {
//			findArrayRange(locSet.sub(0))
//		}
		return null;
	}
	private Set<Term> weakenByIndex(Term pred) {
		Set<Term> result = new HashSet<>();
		Term locSet = findArrayRange(pred.sub(0));
		
		if (locSet != null) {
//			System.out.println("Find Loc Set: "+locSet);
			Term array = locSet.sub(0);
			Term low = locSet.sub(1);
			Term high = locSet.sub(2);
			Term lowToI = null;
			Term iToHigh = null;
//			System.out.println("low: "+ low + ", index: "+ index + ", high: " + high);
			if (sProof.proofLT(low, index)) {
				if (sProof.proofLT(index, high)) {
					
					lowToI = tb.arrayRange(array, low, index);
					iToHigh = tb.arrayRange(array, index, high);
				} else if (sProof.proofEquality(index, high)) {
					lowToI = tb.arrayRange(array, low, index);
					iToHigh = tb.singleton(array, tb.arr(index));
				}
			} else if (sProof.proofEquality(low, index)) {
				if (sProof.proofLT(index, high)) {
					iToHigh = tb.arrayRange(array, index, high);
					lowToI = tb.singleton(array, tb.arr(index));
				} else if(sProof.proofEquality(index, high)) {
					lowToI = tb.singleton(array, tb.arr(index));
					iToHigh = tb.singleton(array, tb.arr(index));
				}
			}	
			if(lowToI!=null && iToHigh!=null) {
				if (pred.op() == depLDT.getNoR()) {
					result.add(tb.noR(lowToI));
					result.add(tb.noR(iToHigh));
				} else if (pred.op() == depLDT.getNoW()) {
					result.add(tb.noW(lowToI));
					result.add(tb.noW(iToHigh));
				} else if (pred.op() == depLDT.getNoRaW()) {
					result.add(tb.noRaW(lowToI));
					result.add(tb.noRaW(iToHigh));
				} else if (pred.op() == depLDT.getNoWaR()) {
					result.add(tb.noWaR(lowToI));
					result.add(tb.noWaR(iToHigh));
				} else if (pred.op() == depLDT.getNoWaW()) {
					result.add(tb.noWaW(lowToI));
					result.add(tb.noWaW(iToHigh));
				}

			}
		}

//		System.out.println(result);
		return result;
	}

	
	private Set<Term> weakeningComparisonPredicates(Term pred) {
		Set<Term> result = new HashSet<>();
		Term low = pred.sub(0);
		Term high = pred.sub(1);
		if (low != null && high != null) {
			if (pred.op() == intLDT.getLessThan()) {
				result.add(tb.leq(low, high));
				result.add(tb.geq(high, low));
			} else if (pred.op() == intLDT.getGreaterThan()) {
				result.add(tb.geq(low, high));
				result.add(tb.leq(high, low));
			} else if (pred.op() == Equality.EQUALS) {
				result.add(tb.geq(low, high));
				result.add(tb.leq(low, high));
			}
		}

		return result;
	}
}