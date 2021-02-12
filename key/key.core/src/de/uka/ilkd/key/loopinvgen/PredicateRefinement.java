package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;
import java.util.Set;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

public class PredicateRefinement {

	public Set<Term> refinedCompList = new HashSet<>();
	public Set<Term> refinedDepList = new HashSet<>();

	private final Sequent seq;
	private Set<Term> depList = new HashSet<>();
	private Set<Term> compList = new HashSet<>();
	private final Services services;
	private final TermBuilder tb;
	private final IntegerLDT intLDT;
	private final DependenciesLDT depLDT;
	private final Set<Operator> CompOps = new HashSet<>();
	private final Function lt, leq, gt, geq;
	private final Operator eq;

	public PredicateRefinement(Services s, Sequent sequent, Set<Term> compPredList, Set<Term> depPredList) {
		services = s;
		tb = services.getTermBuilder();
		compList = compPredList;
		depList = depPredList;
		seq = sequent;

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

	}

	public void readAndRefineAntecedentPredicates() {
		System.out.println("****************************************************");
		Semisequent ante = seq.antecedent();
		for (SequentFormula sf : ante) {
			detectFormula(sf.formula());
		}
//		System.out.println("depList size after delDepPred: " + depList.size());
//		refinedCompList = delRepetitiveCompPred(applyTransitivity(compList));
//		refinedCompList = applyTransitivity(compList);
		refinedCompList = compList;
		refinedDepList = depPredRefineSubSet(delEmptyLocSet(depList));
	}

	void detectFormula(Term sf) {
		for (Operator f : CompOps) {
			if (sf.op().equals(f)) {
//				System.out.println("sf: " + sf);
				delCompPred(sf);
				break;
			}
		}

		if (sf.op().equals(depLDT.getRPred()) || sf.op().equals(depLDT.getWPred())) {
			delDepPred(sf);
		}
		
		else if(sf.op() instanceof UpdateApplication) {
			Term belowupdate = UpdateApplication.getTarget(sf);
			detectFormula(belowupdate);
		}
	}
	
	
	private void delCompPred(Term sf) {
		Term lh = sf.sub(0);
		System.out.println("LH: "+ lh+ "   "+lh.sort());
		Term rh = sf.sub(1);
		System.out.println("RH: " +rh+"   "+rh.sort());
		if (isProgOrLogVars(lh) && isProgOrLogVars(rh)
				&& rh.sort() != services.getTypeConverter().getBooleanType().getSort() /*&& !(rh.sort() instanceof ArraySort) && !(lh.sort() instanceof ArraySort)*/) {

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
				// l == r || r == l
				if ((sf.equals(l_eq_r) || sf.equals(r_eq_l)) && (compT.equals(l_gt_r)
						|| compT.equals(l_lt_r) || compT.equals(r_gt_l) || compT.equals(r_lt_l))) {
					toDelete.add(compT);
					System.out.println(compT + " is deleted because of: " + sf);
				}
				// l > r || r < l
				else if ((sf.equals(l_gt_r) || sf.equals(r_lt_l))
						&& (compT.equals(l_lt_r) || compT.equals(l_leq_r) || compT.equals(l_eq_r)
								|| compT.equals(r_eq_l) || compT.equals(r_gt_l) || compT.equals(r_geq_l))) {
					toDelete.add(compT);
					System.out.println(compT + " is deleted because of: " + sf);
				}
				// l >= r || r <= l
				else if ((sf.equals(r_leq_l) || sf.equals(l_geq_r))
						&& (compT.equals(r_gt_l) || compT.equals(l_lt_r))) {
					toDelete.add(compT);
					System.out.println(compT + " is deleted because of: " + sf);
				}
				// l < r || r > l
				else if ((sf.equals(l_lt_r) || sf.equals(r_gt_l))
						&& (compT.equals(l_gt_r) || compT.equals(l_geq_r) || compT.equals(l_eq_r)
								|| compT.equals(r_eq_l) || compT.equals(r_lt_l) || compT.equals(r_leq_l))) {
					toDelete.add(compT);
					System.out.println(compT + " is deleted because of: " + sf);
				}
				// l <= r || r >= l
				else if ((sf.equals(l_leq_r) || sf.equals(r_geq_l))
						&& (compT.equals(r_lt_l) || compT.equals(l_gt_r))) {
					toDelete.add(compT);
					System.out.println(compT + " is deleted because of: " + sf);
				}
			}
			compList.removeAll(toDelete);
//			System.out.println("Comp List after Refinement: " + compList);
		}
	}

	private Set<Term> applyTransitivity(Set<Term> compPredsList) {
		System.out.println(" applyTransitivity");
		Set<Term> toAdd = new HashSet<>();
		Set<Term> toDelete = new HashSet<>();
//	Set<Term> toDelete = new HashSet<>();
		Semisequent ante = seq.antecedent();
		for (SequentFormula sf1 : ante) {
			Term lh1 = sf1.formula().sub(0);
			Term rh1 = sf1.formula().sub(1);
			Operator op1 = sf1.formula().op();

			if (isProgOrLogVars(lh1) && isProgOrLogVars(rh1)
					&& rh1.sort() != services.getTypeConverter().getBooleanType().getSort()) {
				for (SequentFormula sf2 : ante) {
					Term lh2 = sf2.formula().sub(0);
					Term rh2 = sf2.formula().sub(1);
					Operator op2 = sf2.formula().op();
					
					if (isProgOrLogVars(lh2) && isProgOrLogVars(rh2)
							&& rh2.sort() != services.getTypeConverter().getBooleanType().getSort()) {
//						System.out.println("lh1: " + lh1 + " rh1: " + rh1 + " lh2: " +lh2 + " rh2: " + rh2);
							for (Term t : compList) {
								if ((rh1.equals(lh2) && !lh1.equals(rh2) && t.sub(0).equals(lh1) && t.sub(1).equals(rh2)) 
										|| (lh1.equals(rh2) && !rh1.equals(lh2) && t.sub(0).equals(lh2) && t.sub(1).equals(rh1))) {
									if(compPredsRels(op1, op2, t)) {
										toDelete.add(t);
//										System.out.println(t + " is deleted because of: " + sf1 + " & " + sf2);
									}
							} else if (lh1.equals(lh2) && !rh1.equals(rh2) && t.sub(0).equals(rh1) && t.sub(1).equals(rh2)) {
								if(compPredsRels(op1, op2, t)) {
									toDelete.add(t);
//									System.out.println(t + " is deleted because of: " + sf1 + " & " + sf2);
								}
							} else if (!lh1.equals(lh2) && rh1.equals(rh2) && t.sub(0).equals(lh1) && t.sub(1).equals(lh2)) {
								if(compPredsRels(op1, op2, t)) {
									toDelete.add(t);
//									System.out.println(t + " is deleted because of: " + sf1 + " & " + sf2);
								}
							} 
//							else if (lh1.equals(rh2) && rh1.equals(lh2) && t.sub(0).equals(lh1) && t.sub(1).equals(rh1) && t.op().equals(op1)) {
//								if(delRepetitiveCompPred(op1, op2)) {
//									toDelete.add(t);
//									System.out.println(t + " is deleted because of: " + sf1 + " & " + sf2);
//								}
//							}
						}
					
					}
				}
			}
		}
		compPredsList.removeAll(toDelete);
		System.out.println(compPredsList);
//	System.out.println("Added by trans. " + toAdd);
		return compPredsList;
	}

//	private Set<Term> delRepetitiveCompPred(Set<Term> compPredsList) {//this is not necessary at all
//		System.out.println("REP DEL");
//		Set<Term> toDelete = new HashSet<Term>();
//		for (Term t1 : compPredsList) {
//			Operator op1 = t1.op();
//			for (Term t2 : compPredsList) {
//				Operator op2 = t2.op();
//				if(op1.equals(gt) && op2.equals(lt)) {
//					toDelete.add(t1);
//					toDelete.remove(t2);
//				}
//				else if(op1.equals(geq) && op2.equals(leq)) {
//					toDelete.add(t1);
//					toDelete.remove(t2);
//				}
//				else if(op1.equals(lt) && op2.equals(gt)) {
//					toDelete.add(t1);
//					toDelete.remove(t2);
//				}
//				else if(op1.equals(leq) && op2.equals(geq)) {
//					toDelete.add(t1);
//					toDelete.remove(t2);
//				}
//				else if(op1.equals(geq) && op2.equals(leq)) {
//					toDelete.add(t1);
//					toDelete.remove(t2);
//				}
//				else if(op1.equals(eq) && op2.equals(leq)) {
//					toDelete.add(t1);
//					toDelete.remove(t2);
//				}
//			}
//		}
//		compPredsList.removeAll(toDelete);
//		System.out.println("deleted by REP DEL: " + toDelete);
//		return compPredsList;
//	}

	private boolean compPredsRels(Operator op1, Operator op2, Term t) {
		System.out.println("compPredsRels");
		if (op1.equals(gt) && op2.equals(gt) && (!t.op().equals(gt)) || !t.op().equals(geq)) { // a > b & b > c ==> a > c
			return true;
		} else if (op1.equals(lt) && op2.equals(lt) && (!t.op().equals(lt)) || !t.op().equals(leq)) { // a < b & b < c ==> a < c
			return true;
		} else if (((op1.equals(leq) && op2.equals(leq)) || (op1.equals(leq) && op2.equals(eq))) && t.op().equals(gt)) { // (a <= b & b <= c) || (a <= b & b = c) ==> a <= c
			return true;
		} else if (((op1.equals(geq) && op2.equals(geq)) || (op1.equals(geq) && op2.equals(eq))) && t.op().equals(lt)) { // (a >= b & b >= c) || (a >= b & b = c) ==> a >=c
			return true;
		} else if (((op1.equals(gt) && op2.equals(geq)) || (op1.equals(geq) && op2.equals(gt))
				|| (op1.equals(gt) && op2.equals(eq))) && (!t.op().equals(gt) || !t.op().equals(geq))) { // (a > b & b >= c) || (a >= b & b > c)
															// || (a > b & b = c) ==> a > c
			return true;
		} else if (((op1.equals(leq) && op2.equals(lt)) || ((op1.equals(lt) && op2.equals(leq)))
				|| (op1.equals(lt) && op2.equals(eq))) && (!t.op().equals(lt) || !t.op().equals(leq))) { // (a <= b & b < c) || (a < b & b <= c)
															// || (a < b & b = c) ==> a < c
			return true;
		} else if ((op1.equals(eq) && op2.equals(eq)) && (t.op().equals(lt) || t.op().equals(gt))) { // a = b & b = c ==> a = c
			return true;
		}
		return false;
	}
	
	
	private void delDepPred(Term sf) {
		Operator op = sf.op();
		Term locSet = sf.sub(0);
		Set<Term> toDelete = new HashSet<Term>();

		for (Term t : depList) {
			if (proofNonEmptyIntersection(t.sub(0), locSet)) {
				if (op.equals(depLDT.getRPred()) && t.op().equals(depLDT.getNoR())) {
					toDelete.add(t);
				} else if (op.equals(depLDT.getWPred()) && t.op().equals(depLDT.getNoW())) {
					toDelete.add(t);
				}
			}
		}
		depList.removeAll(toDelete);

	}

	private Set<Term> depPredRefineSubSet(Set<Term> dependencePredicatesSet) {
		Set<Term> toKeep = new HashSet<Term>();

		for (Term t1 : dependencePredicatesSet) {
			if (t1.op().equals(depLDT.getNoRaW()) || t1.op().equals(depLDT.getNoWaR())) {
				for (Term t2 : dependencePredicatesSet) {
					if ((t2.op().equals(depLDT.getNoR()) || t2.op().equals(depLDT.getNoW()))
							&& proofSubSet(t1.sub(0), t2.sub(0))) {
						toKeep.add(t1);
					}
				}
			} else if (t1.op().equals(depLDT.getNoWaW())) {
				for (Term t2 : dependencePredicatesSet) {
					if (t2.op().equals(depLDT.getNoW()) && proofSubSet(t1.sub(0), t2.sub(0))) {
						toKeep.add(t1);
					}
				}
			}

		}
//		System.out.println("toKeep size " + toKeep.size());
		dependencePredicatesSet.removeAll(toKeep);
//		System.out.println("dependencePredicatesSet size after refine by subset: " + dependencePredicatesSet.size());
		Set<Term> refined2 = depPredRefine2(dependencePredicatesSet);
//		System.out.println("Refined by #2 size: " + refined2.size());
		toKeep.addAll(refined2);
//		System.out.println("Size after everything " + toKeep.size());
		return toKeep;
	}

	private Set<Term> depPredRefine2(Set<Term> dependencePredicatesSet) {
		Set<Term> toDelete = new HashSet<Term>();
		Semisequent ante = seq.antecedent();
		Term formulaIntersect = null;

		for (SequentFormula sf1 : ante) {
			if (sf1.formula().op().equals(depLDT.getRPred())) {
				for (SequentFormula sf2 : ante) {
					if (sf2.formula().op().equals(depLDT.getWPred())) {
						if (proofNonEmptyIntersection(sf2.formula().sub(0), sf1.formula().sub(0))) {
							formulaIntersect = tb.intersect(sf1.formula().sub(0), sf2.formula().sub(0));
							if (proofLT(sf2.formula().sub(1), sf1.formula().sub(1))) {
								for (Term term : dependencePredicatesSet) {
									if (term.op().equals(depLDT.getNoRaW())
											&& proofNonEmptyIntersection(term.sub(0), formulaIntersect)) {
										toDelete.add(term);
									}
								}
							} else if (proofLT(sf1.formula().sub(1), sf2.formula().sub(1))) {
								for (Term term : dependencePredicatesSet) {
									if (term.op().equals(depLDT.getNoWaR())) {
										if (proofNonEmptyIntersection(term.sub(0), formulaIntersect)) {
											toDelete.add(term);
										}
									}
								}
							}

						}
					}
				}
			} else if (sf1.formula().op().equals(depLDT.getWPred())) {
				for (SequentFormula sf2 : ante) {
					if (sf2.formula().op().equals(depLDT.getWPred())
							&& proofNonEmptyIntersection(sf2.formula().sub(0), sf1.formula().sub(0))
							&& !sf2.equals(sf1)) {
						formulaIntersect = tb.intersect(sf2.formula().sub(0), sf1.formula().sub(0));
						for (Term term : dependencePredicatesSet) {
							if (term.op().name().equals(depLDT.getNoWaW())) {
								if (proofNonEmptyIntersection(term.sub(0), formulaIntersect)) {
									toDelete.add(term);
								}
							}
						}
					}
				}
			}
		}
		dependencePredicatesSet.removeAll(toDelete);
		return dependencePredicatesSet;
	}

	private Set<Term> delEmptyLocSet(Set<Term> dependencePredicatesSet) {
		Set<Term> toDelete = new HashSet<Term>();
		for (Term term : dependencePredicatesSet) {
			if (proofEmptySet(term.sub(0))) {
				toDelete.add(term);
			}
		}
		dependencePredicatesSet.removeAll(toDelete);
//		System.out.println(" dependencePredicatesSet after removing empty loc sets: " + dependencePredicatesSet.size());
		return dependencePredicatesSet;
	}

	private boolean proofEmptySet(Term loc) {
		Term fml = tb.equals(loc, tb.empty());
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();

		Set<Term> locSetVars = new HashSet<Term>();
		for (Term t : loc.subs()) {
			locSetVars.addAll(getProgAndLogVars(t));
		}

		Set<Term> anteFmlVars = new HashSet<Term>();
		for (SequentFormula sfAnte : seq.antecedent()) {
			anteFmlVars = getProgAndLogVars(sfAnte.formula());
			for (Term tfv : anteFmlVars) {
				if (locSetVars.contains(tfv)) {
					sideSeq = sideSeq.addFormula(sfAnte, true, true).sequent();
					break;
				}
			}
		}

		Set<Term> succFmlVars = new HashSet<Term>();
		for (SequentFormula sfSucc : seq.succedent()) {
			succFmlVars = getProgAndLogVars(sfSucc.formula());
			for (Term tfv : succFmlVars) {
				if (locSetVars.contains(tfv)) {
					sideSeq = sideSeq.addFormula(sfSucc, false, true).sequent();
					break;
				}
			}
		}

		boolean closed = isProvable(sideSeq, services);
		return closed;

	}

	private boolean proofSubSet(Term loc1, Term loc2) {
		Term fml = tb.subset(loc1, loc2);
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();

		Set<Term> locSetVars = new HashSet<Term>();
		for (Term t : loc1.subs()) {
			locSetVars.addAll(getProgAndLogVars(t));
		}
		for (Term t : loc2.subs()) {
			locSetVars.addAll(getProgAndLogVars(t));
		}

		Set<Term> anteFmlVars = new HashSet<Term>();
		for (SequentFormula sfAnte : seq.antecedent()) {
			anteFmlVars = getProgAndLogVars(sfAnte.formula());
			for (Term tfv : anteFmlVars) {
				if (locSetVars.contains(tfv)) {
					sideSeq = sideSeq.addFormula(sfAnte, true, true).sequent();
					break;
				}
			}
		}

		Set<Term> succFmlVars = new HashSet<Term>();
		for (SequentFormula sfSucc : seq.succedent()) {
			succFmlVars = getProgAndLogVars(sfSucc.formula());
			for (Term tfv : succFmlVars) {
				if (locSetVars.contains(tfv)) {
					sideSeq = sideSeq.addFormula(sfSucc, false, true).sequent();
					break;
				}
			}
		}

		boolean closed = isProvable(sideSeq, services);
		// true: Holds, false: Unknown
//		System.out.println("Subset proof" + ProofSaver.printAnything(sideSeq, services));// Human readable v
//		if (closed) {
//			System.out.println("This proof is closed:  " + sideSeq);
//		}
		return closed;
	}

	private boolean proofLT(Term ts1, Term ts2) {
		Term fml = tb.lt(ts1, ts2);
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();

		Set<Term> locSetVars = new HashSet<Term>();
		for (Term t : ts1.subs()) {
			locSetVars.addAll(getProgAndLogVars(t));
		}
		for (Term t : ts2.subs()) {
			locSetVars.addAll(getProgAndLogVars(t));
		}

		Set<Term> anteFmlVars = new HashSet<Term>();
		for (SequentFormula sfAnte : seq.antecedent()) {
			anteFmlVars = getProgAndLogVars(sfAnte.formula());
			for (Term tfv : anteFmlVars) {
				if (locSetVars.contains(tfv)) {
					sideSeq = sideSeq.addFormula(sfAnte, true, true).sequent();
					break;
				}
			}
		}

		Set<Term> succFmlVars = new HashSet<Term>();
		for (SequentFormula sfSucc : seq.succedent()) {
			succFmlVars = getProgAndLogVars(sfSucc.formula());
			for (Term tfv : succFmlVars) {
				if (locSetVars.contains(tfv)) {
					sideSeq = sideSeq.addFormula(sfSucc, false, true).sequent();
					break;
				}
			}
		}

		boolean closed = isProvable(sideSeq, services);
		return closed;
	}

	private boolean proofNonEmptyIntersection(Term ts1, Term ts2) {
		Term fml = tb.not(tb.equals(tb.intersect(ts1, ts2), tb.empty()));
		Set<Term> locSetVars = new HashSet<Term>();
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();

		for (Term t : ts1.subs())
			locSetVars.addAll(getProgAndLogVars(t));
		for (Term t : ts2.subs())
			locSetVars.addAll(getProgAndLogVars(t));

		Set<Term> anteFmlVars = new HashSet<Term>();
		for (SequentFormula sfAnte : seq.antecedent()) {
			anteFmlVars = getProgAndLogVars(sfAnte.formula());
			for (Term tfv : anteFmlVars) {
				if (locSetVars.contains(tfv)) {
					sideSeq = sideSeq.addFormula(sfAnte, true, true).sequent();
					break;
				}
			}
		}

		Set<Term> succFmlVars = new HashSet<Term>();
		for (SequentFormula sfSucc : seq.succedent()) {
			succFmlVars = getProgAndLogVars(sfSucc.formula());
			for (Term tfv : succFmlVars) {
				if (locSetVars.contains(tfv)) {
					sideSeq = sideSeq.addFormula(sfSucc, false, true).sequent();
					break;
				}
			}
		}
		boolean closed = isProvable(sideSeq, services);
		return closed;
	}

	protected boolean isProvable(Sequent seq2prove, Services services) {
		final ProofStarter ps = new ProofStarter(false);
//		System.out.println("proof " + ProofSaver.printAnything(seq, services));

		final ProofEnvironment env = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());
		try {
			ps.init(seq2prove, env, "IsInRange Proof");
		} catch (ProofInputException pie) {
			pie.printStackTrace();
			return false;
		}

		final StrategyProperties sp = ps.getProof().getActiveStrategyFactory().getSettingsDefinition()
				.getDefaultPropertiesFactory().createDefaultStrategyProperties();
		sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_OFF);
		ps.setStrategyProperties(sp);

		ps.getProof().getSettings().getStrategySettings().setActiveStrategyProperties(sp);

		ps.setMaxRuleApplications(10000);
		ps.setTimeout(-1);
//		System.out.println("strategy prop. " + sp);

		final ApplyStrategyInfo info = ps.start();
//		System.out.println("rules: "+ ps.getProof().getStatistics());
//		if (!info.getProof().closed()) {
//			System.out.println("Open Goals: " + info.getProof().openGoals());
//		}
		return info.getProof().closed();
	}

//	Term expr2term(Expression expr) {
//		return this.services.getTypeConverter().convertToLogicElement(expr);
//	}

	private Set<Term> getProgAndLogVars(Term term) {

		Set<Term> res = new HashSet<Term>();
		if (!term.containsJavaBlockRecursive()) {
			if (term.op() instanceof ProgramVariable)
				res.add(term);
			else if (term.op() instanceof Function && term.sort() != Sort.FORMULA
					&& (term.arity() == 0 || term.arity() == 1) && term.freeVars().isEmpty())
				res.add(term);

			else
				for (Term sub : term.subs())
					res.addAll(getProgAndLogVars(sub));
		}
		return res;
	}

	private boolean isProgOrLogVars(Term term) {

		if (!term.containsJavaBlockRecursive()) {
			if (term.op() instanceof ProgramVariable) {
				return true;
			} else if (term.op() instanceof Function && term.sort() != Sort.FORMULA
					&& (term.arity() == 0 || term.arity() == 1) && term.freeVars().isEmpty()) {
				return true;
			} else
				for (Term sub : term.subs())
					isProgOrLogVars(sub);
		}
		return false;
	}

}
