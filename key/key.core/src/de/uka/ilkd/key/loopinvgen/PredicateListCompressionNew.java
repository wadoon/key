package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;
import java.util.Set;

import com.sun.org.apache.xpath.internal.operations.Equals;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;

public class PredicateListCompressionNew {
	private final DependenciesLDT depLDT;
	private final Services services;
	private final TermBuilder tb;
	private final Sequent seq;
//	private final SequentFormula currentIdxF;
	private final IntegerLDT intLDT;
	private final Set<Operator> CompOps = new HashSet<>();
	private final Function lt, leq, gt, geq;
	private SideProof sProof;
	private final boolean ailias;
	private Set<Term> allPreds = new HashSet<>();

	public PredicateListCompressionNew(Services s, Sequent sequent, Set<Term> preds, boolean ailiasing) {
		services = s;
		tb = services.getTermBuilder();
		seq = sequent;
//		currentIdxF = currentIndexFormula;
		depLDT = services.getTypeConverter().getDependenciesLDT();

		intLDT = services.getTypeConverter().getIntegerLDT();
		lt = intLDT.getLessThan();
		CompOps.add(lt);
		leq = intLDT.getLessOrEquals();
		CompOps.add(leq);
		gt = intLDT.getGreaterThan();
		CompOps.add(gt);
		geq = intLDT.getGreaterOrEquals();
		CompOps.add(geq);
		sProof = new SideProof(services, seq, 500);
		ailias = ailiasing;
		allPreds = preds;
	}

	public Set<Term> compression() {

		Set<Term> compPredsList = new HashSet<>();
		Set<Term> depPredsList = new HashSet<>();
		Set<Term> result = new HashSet<>();
		for (Term term : allPreds) {
			if (term.op().equals(depLDT.getNoR()) || term.op().equals(depLDT.getNoW())
					|| term.op().equals(depLDT.getNoRaW()) || term.op().equals(depLDT.getNoWaR())
					|| term.op().equals(depLDT.getNoWaW())) {
				depPredsList.add(term);
			} else if (term.op().equals(lt) || term.op().equals(leq) || term.op().equals(gt) || term.op().equals(geq) || term.op().equals(Equality.EQUALS)) {
				compPredsList.add(term);
			}
		}
		result.addAll(finalCompPredListCompression(compPredsList));
		result.addAll(depPredListCompressionBySubset(depPredsList));
		return result;

	}

	private Set<Term> depPredListCompressionBySubset(Set<Term> fDepPredList) {
		Set<Term> toDelete = new HashSet<>();

		for (Term depPred1 : fDepPredList) {
			for (Term depPred2 : fDepPredList) {
				if (depPred1.op().equals(depPred2.op()) && !depPred1.sub(0).equals(depPred2.sub(0))
						&& depPred1.sub(0).sub(0).equals(depPred2.sub(0).sub(0))) {
					Boolean loc1SubSetloc2 = sProof.proofSubSet(depPred1.sub(0), depPred2.sub(0));

					if (loc1SubSetloc2) {
						toDelete.add(depPred1);
					} else {
						Boolean loc2SubSetloc1 = sProof.proofSubSet(depPred2.sub(0), depPred1.sub(0));
						if (loc2SubSetloc1)
							toDelete.add(depPred2);
					}
				}
			}
		}
		fDepPredList.removeAll(toDelete);
//		fDepPredList = refineAiliasing(fDepPredList, toDelete);
		toDelete.removeAll(toDelete);

		for (Term depPred1 : fDepPredList) {
			for (Term depPred2 : fDepPredList) {
				if (depPred1.op().equals(depLDT.getNoR())) {
					if (depPred2.op().equals(depLDT.getNoRaW()) || depPred2.op().equals(depLDT.getNoWaR())) {
						if (sProof.proofSubSet(depPred2.sub(0), depPred1.sub(0))) {
							toDelete.add(depPred2);
						}
					}
				} else if (depPred1.op().equals(depLDT.getNoW())) {
					if (depPred2.op().equals(depLDT.getNoRaW()) || depPred2.op().equals(depLDT.getNoWaR())
							|| depPred2.op().equals(depLDT.getNoWaW())) {
						if (sProof.proofSubSet(depPred2.sub(0), depPred1.sub(0))) {
							toDelete.add(depPred2);
						}
					}
				}
			}
		}
		fDepPredList.removeAll(toDelete);
//		fDepPredList = refineAiliasing(fDepPredList, toDelete);
//		System.out.println("deleted by compression: " + toDelete);
		toDelete.removeAll(toDelete);

		if (ailias) {
			for (Term depPred1 : fDepPredList) {
				for (Term depPred2 : fDepPredList) {
					if (depPred1.op().equals(depPred2.op()) && !depPred1.sub(0).sub(0).equals(depPred2.sub(0).sub(0))) {
						if (sProof.proofEquality(depPred1.sub(0), depPred2.sub(0))) {
							if (!toDelete.contains(depPred2)) {
								toDelete.add(depPred1);
							}
						}
					}
				}
			}
		}

		fDepPredList.removeAll(toDelete);

		return fDepPredList;
	}

	private Set<Term> finalCompPredListCompression(Set<Term> fCompPredList) {
		Set<Term> toDelete = new HashSet<>();
		for (Term compPred1 : fCompPredList) {
			for (Term compPred2 : fCompPredList) {
				if (compPred1.sub(0).equals(compPred2.sub(0)) && compPred1.sub(1).equals(compPred2.sub(1))) { // a X b
																												// && a
																												// Y b
					if (compPred1.op().equals(geq) && compPred2.op().equals(gt)) {
						toDelete.add(compPred2);
					} else if (compPred1.op().equals(gt) && compPred2.op().equals(geq)) {
						toDelete.add(compPred1);
					} else if (compPred1.op().equals(leq) && compPred2.op().equals(lt)) {
						toDelete.add(compPred2);
					} else if (compPred1.op().equals(lt) && compPred2.op().equals(leq)) {
						toDelete.add(compPred1);
					} if (compPred1.op().equals(Equality.EQUALS) && compPred2.op().equals(geq)) {
						toDelete.add(compPred1);
					} else if (compPred1.op().equals(Equality.EQUALS) && compPred2.op().equals(leq)) {
						toDelete.add(compPred1);
					}
					
				} else if (compPred1.sub(0).equals(compPred2.sub(1)) && compPred1.sub(1).equals(compPred2.sub(0))) { // a
																														// X
																														// b
																														// &&
																														// b
																														// Y
																														// a
					if (compPred1.op().equals(gt) && compPred2.op().equals(lt)) {
						toDelete.add(compPred1);
					} else if (compPred1.op().equals(lt) && compPred2.op().equals(gt)) {
						toDelete.add(compPred2);
					} else if (compPred1.op().equals(geq) && compPred2.op().equals(leq)) {
						toDelete.add(compPred1);
					} else if (compPred1.op().equals(leq) && compPred2.op().equals(geq)) {
						toDelete.add(compPred2);
					} if (compPred1.op().equals(Equality.EQUALS) && compPred2.op().equals(geq)) {
						toDelete.add(compPred1);
					} else if (compPred1.op().equals(Equality.EQUALS) && compPred2.op().equals(leq)) {
						toDelete.add(compPred1);
					}
				}

			}
		}
		fCompPredList.removeAll(toDelete);
//		System.out.println("deleted by compression: " + toDelete);
		return fCompPredList;
	}
}
