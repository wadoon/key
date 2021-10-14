package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;
import java.util.Set;

import antlr.NameSpace;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.io.ProofSaver;

public class PredicateRefinement {

	public Set<Term> refinedCompList;
	public Set<Term> refinedDepList;

	private final Sequent seq;
	private Set<Term> depList = new HashSet<>();
	private Set<Term> compList = new HashSet<>();
	private final Services services;
	private final TermBuilder tb;
	private final SequentFormula currentIdxF;
	private final IntegerLDT intLDT;
	private final DependenciesLDT depLDT;
	private final Set<Operator> CompOps = new HashSet<>();
	private final Function lt, leq, gt, geq;
	private final Operator eq;
	private SideProof sProof;

	public PredicateRefinement(Services s, Sequent sequent, Set<Term> compPredList, Set<Term> depPredList,
			SequentFormula currentIndexFormula) {
		services = s;
		tb = services.getTermBuilder();
		compList = compPredList;
		depList = depPredList;
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
		eq = Equality.EQUALS;
		CompOps.add(eq);

		sProof = new SideProof(services, seq);
	}

	public void readAndRefineAntecedentPredicates() {
		Semisequent ante = seq.antecedent();
		for (SequentFormula sf : ante) {
			detectFormula(sf.formula());
		}
	}

	private void detectFormula(Term sf) {
		for (Operator f : CompOps) {
			if (sf.op().equals(f)) {
				delCompPred(sf);
				refinedCompList = compList;
				break;
			}
		}
		if (sf.op().equals(depLDT.getRPred()) || sf.op().equals(depLDT.getWPred())) {
			delDepPred(sf, depList);
		} else if (sf.op() instanceof UpdateApplication) { // TODO: check if it is correct. Because it ignores the effect
															// of the update.
			System.out.println("Update " + sf);
		}
		
		else if(sf.op().name().toString().equals("if-then-else")){
			conditionalDelDepPred(sf, depList);
		}
		refinedDepList = depList;
	}

	private void conditionalDelDepPred(Term sf, Set<Term> depList) {
//		Operator pred = sf.op();
////		System.out.println("AAAA====> " + ProofSaver.printAnything(sf, services));				
//		
//		Term locSet = sf.sub(0);
//		Set<Term> toDelete = new HashSet<Term>();
//		Set<Term> tempDelete = new HashSet<Term>();
//		for (Term t : depList) {
//			if (pred.equals(depLDT.getRPred()) && t.op().equals(depLDT.getNoR())) {
//				if (sProof.proofNonEmptyIntersection(t.sub(0), locSet)) {
//					toDelete.add(t);
//				}
//			} else if (pred.equals(depLDT.getWPred()) && t.op().equals(depLDT.getNoW())) {
////System.out.println("Checking for " + ProofSaver.printAnything(t, services));				
//				if (sProof.proofNonEmptyIntersection(t.sub(0), locSet)) {
//					toDelete.add(t);
//				}
//			}
//		}
//		dpList.removeAll(toDelete);
//		depPredRefine(sf, dpList);
		
	}

	private void delCompPred(Term sf) {
		Term lh = sf.sub(0);
		Term rh = sf.sub(1);
		if (isProgramOrLogicVariable(lh) && isProgramOrLogicVariable(rh)
				&& rh.sort() != services.getTypeConverter().getBooleanType().getSort()
				&& lh.sort() != services.getTypeConverter().getBooleanType().getSort()
				&& !(rh.sort() instanceof ArraySort) && !(lh.sort() instanceof ArraySort)) {

			Term l_eq_r = tb.equals(lh, rh);
			Term r_eq_l = tb.equals(rh, lh);
			Term l_gt_r = tb.gt(lh, rh);
			Term r_gt_l = tb.gt(rh, lh);
			Term l_geq_r = tb.geq(lh, rh);
			Term r_geq_l = tb.geq(rh, lh);
			Term l_lt_r = tb.lt(lh, rh);
			Term r_lt_l = tb.lt(rh, lh);
			Term l_leq_r = tb.leq(lh, rh);
			Term r_leq_l = tb.leq(rh, lh);

			Set<Term> toDelete = new HashSet<Term>();

			for (Term compT : compList) {
				if ((compT.sub(0).equals(lh) && compT.sub(1).equals(rh))
						|| (compT.sub(0).equals(rh) && compT.sub(1).equals(lh))) {
					// l == r
					if (sf.op().equals(eq) && (compT.equals(l_gt_r) || compT.equals(l_lt_r) || compT.equals(r_gt_l)
							|| compT.equals(r_lt_l))) {
						toDelete.add(compT);
					}

					// l > r
					else if (sf.op().equals(gt)
							&& (compT.equals(l_lt_r) || compT.equals(l_leq_r) || compT.equals(l_eq_r)
									|| compT.equals(r_eq_l) || compT.equals(r_gt_l) || compT.equals(r_geq_l))) {
						toDelete.add(compT);
					}
					// l >= r
					else if (sf.op().equals(geq) && (compT.equals(r_gt_l) || compT.equals(l_lt_r))) {
						toDelete.add(compT);
					}
					// l < r
					else if (sf.equals(lt) && (compT.equals(l_gt_r) || compT.equals(l_geq_r) || compT.equals(l_eq_r)
							|| compT.equals(r_eq_l) || compT.equals(r_lt_l) || compT.equals(r_leq_l))) {
						toDelete.add(compT);
					}
					// l <= r
					else if (sf.equals(l_leq_r) && (compT.equals(r_lt_l) || compT.equals(l_gt_r))) {
						toDelete.add(compT);
					}

				} else if (compT.sub(0).equals(lh)) {
					toDelete.addAll(oneSideMatch(sf, compT, rh, compT.sub(1)));
				} else if (compT.sub(1).equals(rh)) {
					toDelete.addAll(oneSideMatch(sf, compT, lh, compT.sub(0)));
				} else if (compT.sub(1).equals(lh)) {
					toDelete.addAll(oneSideMatch(sf, compT, rh, compT.sub(0)));
				} else if (compT.sub(0).equals(rh)) {
					toDelete.addAll(oneSideMatch(sf, compT, lh, compT.sub(1)));
				}
			}
			compList.removeAll(toDelete);
		}
	}

	private Set<Term> oneSideMatch(Term sf, Term compT, Term rh, Term x) {
		Set<Term> toDelete = new HashSet<Term>();
		// l == r
		if (sf.op().equals(eq)) {
			// l == x
			if (compT.op().equals(eq)) {
				// because definitely rh != x
				toDelete.add(compT);
			}
			// l >= x || l > x
			else if (compT.op().equals(geq) || compT.op().equals(gt)) {
				if (sProof.proofLT(rh, x)) {
					toDelete.add(compT);
				}
			}
			// l <= x || l < x
			else if (compT.op().equals(leq) || compT.op().equals(lt)) {
				if (sProof.proofLT(x, rh)) {
					toDelete.add(compT);
				}
			}
		}
		// l > r || l >= r
		else if (sf.op().equals(gt) || sf.op().equals(geq)) {
			// l == x || l <= x || l < x
			if (compT.op().equals(eq) || compT.op().equals(leq) || compT.op().equals(lt)) {
				if (sProof.proofLT(x, rh)) {
					toDelete.add(compT);
				}
			}
		}
		// l < r || l <= r
		else if (sf.op().equals(lt) || sf.op().equals(leq)) {
			// l == x || l >= x || l > x
			if (compT.op().equals(eq) || compT.op().equals(geq) || compT.op().equals(gt)) {
				if (sProof.proofLT(rh, x)) {
					toDelete.add(compT);
				}
			}
		}
		return toDelete;
	}

	private void delDepPred(Term sf, Set<Term> dpList) {
		Operator pred = sf.op();
//		System.out.println("AAAA====> " + ProofSaver.printAnything(sf, services));				
		
		Term locSet = sf.sub(0);
		Set<Term> toDelete = new HashSet<Term>();
		Set<Term> tempDelete = new HashSet<Term>();
		for (Term t : dpList) {
			if (pred.equals(depLDT.getRPred()) && t.op().equals(depLDT.getNoR())) {
				if (sProof.proofNonEmptyIntersection(t.sub(0), locSet)) {
					toDelete.add(t);
				}
			} else if (pred.equals(depLDT.getWPred()) && t.op().equals(depLDT.getNoW())) {
//System.out.println("Checking for " + ProofSaver.printAnything(t, services));				
				if (sProof.proofNonEmptyIntersection(t.sub(0), locSet)) {
					toDelete.add(t);
				}
			}
		}
		dpList.removeAll(toDelete);
		depPredRefine(sf, dpList);
	}

	private void depPredRefine(Term sf, Set<Term> dependencePredicatesSet) {
		Set<Term> toDelete = new HashSet<Term>();
		Semisequent ante = seq.antecedent();
		Term formulaIntersect = null;

			if (sf.op().equals(depLDT.getRPred())) {
				for (SequentFormula sf2 : ante) {
					if (sf2.formula().op().equals(depLDT.getWPred())) {
						if (sProof.proofNonEmptyIntersection(sf2.formula().sub(0), sf.sub(0))) {
							formulaIntersect = tb.intersect(sf.sub(0), sf2.formula().sub(0));
							if (sProof.proofLT(sf2.formula().sub(1), sf.sub(1))) {
								for (Term term : dependencePredicatesSet) {
									if (term.op().equals(depLDT.getNoRaW()) && sProof.proofNonEmptyIntersection(
											term.sub(0), formulaIntersect)) {
										toDelete.add(term);
									}
								}
							} else if (sProof.proofLT(sf.sub(1), sf2.formula().sub(1))) {
								for (Term term : dependencePredicatesSet) {
									if (term.op().equals(depLDT.getNoWaR())) {
										if (sProof.proofNonEmptyIntersection(term.sub(0), formulaIntersect)) {
											toDelete.add(term);
										}
									}
								}
							}
						}
					}
				}
			} else if (sf.op().equals(depLDT.getWPred())) {
				for (SequentFormula sf2 : ante) {
					if (sf2.formula().op().equals(depLDT.getWPred()) && sProof.proofNonEmptyIntersection(
							sf2.formula().sub(0), sf.sub(0)) && !sf2.equals(sf)) {
						formulaIntersect = tb.intersect(sf2.formula().sub(0), sf.sub(0));
						for (Term term : dependencePredicatesSet) {
							if (term.op().name().equals(depLDT.getNoWaW())) {
								if (sProof.proofNonEmptyIntersection(term.sub(0), formulaIntersect)) {
									toDelete.add(term);
								}
							}
						}
					}
				}
			}
		dependencePredicatesSet.removeAll(toDelete);
	}

	private boolean isProgramOrLogicVariable(Term term) {

		if (!term.containsJavaBlockRecursive()) {
			if (term.op() instanceof ProgramVariable) {
//				System.out.println("PV " + term);
				return true;
			} else if (term.op() instanceof Function && term.sort() != Sort.FORMULA
					&& (term.arity() == 0 || term.arity() == 1) && term.freeVars().isEmpty()) {
//				System.out.println("FUNCTION " + term);
				return true;
			} else
				for (Term sub : term.subs()) {
					isProgramOrLogicVariable(sub);
//					System.out.println("SUB " + sub);
				}

		}
		return false;
	}
}