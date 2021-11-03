//package de.uka.ilkd.key.loopinvgen;
//
//import java.util.HashSet;
//import java.util.Set;
//
//import de.uka.ilkd.key.java.Services;
//import de.uka.ilkd.key.ldt.IntegerLDT;
//import de.uka.ilkd.key.logic.Term;
//import de.uka.ilkd.key.logic.TermBuilder;
//import de.uka.ilkd.key.logic.op.Equality;
//import de.uka.ilkd.key.logic.op.Function;
//import de.uka.ilkd.key.logic.op.Operator;
//import de.uka.ilkd.key.logic.op.ProgramVariable;
//import de.uka.ilkd.key.logic.sort.ArraySort;
//import de.uka.ilkd.key.logic.sort.Sort;
//
//public class RefineByGuard {
//	private final Services services;
//	private final TermBuilder tb;
//	private Set<Term> compList = new HashSet<>();
//	private final Term guard;
//	private final Function lt, leq, gt, geq;
//	private final Operator eq;
//	private final IntegerLDT intLDT;
//	private final Set<Operator> CompOps = new HashSet<>();
//	private SideProof sProof;
//
//	public RefineByGuard(Services s, Set<Term> compPredList, Term g) {
//		services = s;
//		tb = services.getTermBuilder();
//		compList = compPredList;
//		guard = g;
//
//		intLDT = services.getTypeConverter().getIntegerLDT();
//		lt = intLDT.getLessThan();
//		CompOps.add(lt);
//		leq = intLDT.getLessOrEquals();
//		CompOps.add(leq);
//		gt = intLDT.getGreaterThan();
//		CompOps.add(gt);
//		geq = intLDT.getGreaterOrEquals();
//		CompOps.add(geq);
//		eq = Equality.EQUALS;
//		CompOps.add(eq);
//		delCompPred();
//
//	}
//
//	public Set<Term> delCompPred() {
//		Term lh = guard.sub(0);
//		Term rh = guard.sub(1);
//		if (isProgramOrLogicVariable(lh) && isProgramOrLogicVariable(rh)
//				&& rh.sort() != services.getTypeConverter().getBooleanType().getSort()
//				&& lh.sort() != services.getTypeConverter().getBooleanType().getSort()
//				&& !(rh.sort() instanceof ArraySort) && !(lh.sort() instanceof ArraySort)) {
//
//			Term l_eq_r = tb.equals(lh, rh);
//			Term r_eq_l = tb.equals(rh, lh);
//			Term l_gt_r = tb.gt(lh, rh);
//			Term r_gt_l = tb.gt(rh, lh);
//			Term l_geq_r = tb.geq(lh, rh);
//			Term r_geq_l = tb.geq(rh, lh);
//			Term l_lt_r = tb.lt(lh, rh);
//			Term r_lt_l = tb.lt(rh, lh);
//			Term l_leq_r = tb.leq(lh, rh);
//			Term r_leq_l = tb.leq(rh, lh);
//
//			Set<Term> toDelete = new HashSet<Term>();
//
//			for (Term compT : compList) {
//				if ((compT.sub(0).equals(lh) && compT.sub(1).equals(rh))
//						|| (compT.sub(0).equals(rh) && compT.sub(1).equals(lh))) {
//					// l == r
//					if (guard.op().equals(eq) && (compT.equals(l_gt_r) || compT.equals(l_lt_r) || compT.equals(r_gt_l)
//							|| compT.equals(r_lt_l))) {
//						toDelete.add(compT);
//					}
//
//					// l > r
//					else if (guard.op().equals(gt)
//							&& (compT.equals(l_lt_r) || compT.equals(l_leq_r) || compT.equals(l_eq_r)
//									|| compT.equals(r_eq_l) || compT.equals(r_gt_l) || compT.equals(r_geq_l))) {
//						toDelete.add(compT);
//					}
//					// l >= r
//					else if (guard.op().equals(geq) && (compT.equals(r_gt_l) || compT.equals(l_lt_r))) {
//						toDelete.add(compT);
//					}
//					// l < r
//					else if (guard.equals(lt) && (compT.equals(l_gt_r) || compT.equals(l_geq_r) || compT.equals(l_eq_r)
//							|| compT.equals(r_eq_l) || compT.equals(r_lt_l) || compT.equals(r_leq_l))) {
//						toDelete.add(compT);
//					}
//					// l <= r
//					else if (guard.equals(l_leq_r) && (compT.equals(r_lt_l) || compT.equals(l_gt_r))) {
//						toDelete.add(compT);
//					}
//
//				} else if (compT.sub(0).equals(lh)) {
//					toDelete.addAll(oneSideMatch(guard, compT, rh, compT.sub(1)));
//				} else if (compT.sub(1).equals(rh)) {
//					toDelete.addAll(oneSideMatch(guard, compT, lh, compT.sub(0)));
//				} else if (compT.sub(1).equals(lh)) {
//					toDelete.addAll(oneSideMatch(guard, compT, rh, compT.sub(0)));
//				} else if (compT.sub(0).equals(rh)) {
//					toDelete.addAll(oneSideMatch(guard, compT, lh, compT.sub(1)));
//				}
//			}
//			compList.removeAll(toDelete);
//		}
//		return compList;
//	}
//
//	private Set<Term> oneSideMatch(Term sf, Term compT, Term rh, Term x) {
//		Set<Term> toDelete = new HashSet<Term>();
//		// l == r
//		if (sf.op().equals(eq)) {
//			// l == x
//			if (compT.op().equals(eq)) {
//				// because definitely rh != x
//				toDelete.add(compT);
//			}
//			// l >= x || l > x
//			else if (compT.op().equals(geq) || compT.op().equals(gt)) {
//				if (sProof.proofLT(rh, x)) {
//					toDelete.add(compT);
//				}
//			}
//			// l <= x || l < x
//			else if (compT.op().equals(leq) || compT.op().equals(lt)) {
//				if (sProof.proofLT(x, rh)) {
//					toDelete.add(compT);
//				}
//			}
//		}
//		// l > r || l >= r
//		else if (sf.op().equals(gt) || sf.op().equals(geq)) {
//			// l == x || l <= x || l < x
//			if (compT.op().equals(eq) || compT.op().equals(leq) || compT.op().equals(lt)) {
//				if (sProof.proofLT(x, rh)) {
//					toDelete.add(compT);
//				}
//			}
//		}
//		// l < r || l <= r
//		else if (sf.op().equals(lt) || sf.op().equals(leq)) {
//			// l == x || l >= x || l > x
//			if (compT.op().equals(eq) || compT.op().equals(geq) || compT.op().equals(gt)) {
//				if (sProof.proofLT(rh, x)) {
//					toDelete.add(compT);
//				}
//			}
//		}
//		return toDelete;
//	}
//
//	private boolean isProgramOrLogicVariable(Term term) {
//
//		if (!term.containsJavaBlockRecursive()) {
//			if (term.op() instanceof ProgramVariable) {
////				System.out.println("PV " + term);
//				return true;
//			} else if (term.op() instanceof Function && term.sort() != Sort.FORMULA
//					&& (term.arity() == 0 || term.arity() == 1) && term.freeVars().isEmpty()) {
////				System.out.println("FUNCTION " + term);
//				return true;
//			} else
//				for (Term sub : term.subs()) {
//					isProgramOrLogicVariable(sub);
////					System.out.println("SUB " + sub);
//				}
//
//		}
//		return false;
//	}
//
//}
