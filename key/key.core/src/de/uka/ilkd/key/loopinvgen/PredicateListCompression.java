package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;

public class PredicateListCompression {
	private final DependenciesLDT depLDT;
	private final Services services;
	private final TermBuilder tb;
	private final Sequent seq;
	private final SequentFormula currentIdxF;
	private final IntegerLDT intLDT;
	private final Set<Operator> CompOps = new HashSet<>();
	private final Function lt, leq, gt, geq;
	private SideProof sProof;

	public PredicateListCompression(Services s, Sequent sequent, SequentFormula currentIndexFormula) {
		services = s;
		tb = services.getTermBuilder();
		seq = sequent;
		currentIdxF = currentIndexFormula;
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
		sProof = new SideProof(services, seq);
	}

	void compression(Set<Term> depPredsList, Set<Term> compPredsList) {

//		do {

//			oldDepPredsList.removeAll(oldDepPredsList);
//			oldDepPredsList.addAll(depPredsList);

		finalCompPredListCompression(compPredsList);
//		finalDepPredListCompression(depPredsList);

//		} while(/*!compPredsList.equals(oldCompPredsList) || */depPredsList.size()!=oldDepPredsList.size());// Logically it is not a valid condition but also !depPredsList.equal(oldDepPreds) is not working correctly because it is checking syntactic equality 

//		System.out.println("LIG is the conjunction of: " + compPredsList + "  size " + compPredsList.size() + " and "
//				+ depPredsList + " of size " + depPredsList.size());
	}

	private Set<Term> finalDepPredListCompression(Set<Term> fDepPredList) {
		Set<Term> toDelete = new HashSet<>();
		Set<Term> toAdd = new HashSet<>();
		for (Term depPred1 : fDepPredList) {
			for (Term depPred2 : fDepPredList) {
				if (depPred1.op().equals(depPred2.op()) && !depPred1.sub(0).equals(depPred2.sub(0))
						&& depPred1.sub(0).sub(0).equals(depPred2.sub(0).sub(0))) {
					Boolean loc1SubSetloc2 = sProof.proofSubSetWIndex(currentIdxF, depPred1.sub(0), depPred2.sub(0));
					Boolean loc2SubSetloc1 = sProof.proofSubSetWIndex(currentIdxF, depPred2.sub(0), depPred1.sub(0));
					if (loc1SubSetloc2 && !loc2SubSetloc1) {
						toDelete.add(depPred1);
					} else if (loc2SubSetloc1 && !loc1SubSetloc2) {
						toDelete.add(depPred2);
					} else if (!loc1SubSetloc2 && !loc2SubSetloc1) { // this adds uniond and locSet doesn't have proper
																		// rules for them. That is why I'm not
																		// compressing dep preds now.
						toDelete.add(depPred1);
						toDelete.add(depPred2);
						if (depPred1.op().equals(depLDT.getNoR())) {
							toAdd.add(tb.noR(tb.union(depPred1.sub(0), depPred2.sub(0))));
						} else if (depPred1.op().equals(depLDT.getNoW())) {
							toAdd.add(tb.noW(tb.union(depPred1.sub(0), depPred2.sub(0))));
						} else if (depPred1.op().equals(depLDT.getNoRaW())) {
							toAdd.add(tb.noRaW(tb.union(depPred1.sub(0), depPred2.sub(0))));
						} else if (depPred1.op().equals(depLDT.getNoWaR())) {
							toAdd.add(tb.noWaR(tb.union(depPred1.sub(0), depPred2.sub(0))));
						} else if (depPred1.op().equals(depLDT.getNoWaW())) {
							toAdd.add(tb.noWaW(tb.union(depPred1.sub(0), depPred2.sub(0))));
						}
					}
				}
			}
		}
//		System.out.println(toDelete.size());
		fDepPredList.addAll(toAdd);
		// Following lines are basically fDepPredList.removeAll(toDelete) plus being
		// semmantically correct
		fDepPredList.removeAll(toDelete);
		Set<Term> delete = new HashSet<>();
		for (Term del : toDelete) {
			for (Term pred : fDepPredList) {
				if (del.op().equals(pred.op()) && sProof.proofSubSetWIndex(currentIdxF, del.sub(0), pred.sub(0))
						&& sProof.proofSubSetWIndex(currentIdxF, pred.sub(0), del.sub(0))) {
					delete.add(pred);
				}
			}
		}
		fDepPredList.removeAll(delete);
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
					}
				}

			}
		}
		fCompPredList.removeAll(toDelete);
		return fCompPredList;
	}	
}
