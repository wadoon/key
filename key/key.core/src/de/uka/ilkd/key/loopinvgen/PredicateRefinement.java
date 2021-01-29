package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;
import java.util.Set;
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
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

public class PredicateRefinement {

	private Set<Term> depList;
	public Set<Term> refinedDepList;
	private Set<Term> compList = new HashSet<Term>();
	public Set<Term> refinedCompList;
	private final Services services;
	private final TermBuilder tb;
	private final IntegerLDT intLDT;
	private final DependenciesLDT depLDT;
	private final Set<Operator> CompOps = new HashSet<>();

	public PredicateRefinement(Services s, Sequent sequent, Set<Term> compPredList, Set<Term> depPredList) {
		services = s;
		tb = services.getTermBuilder();
		compList = compPredList;
		depList = depPredList;

		depLDT = services.getTypeConverter().getDependenciesLDT();

		intLDT = services.getTypeConverter().getIntegerLDT();
		Function lt = intLDT.getLessThan();
		CompOps.add(lt);
		Function leq = intLDT.getLessOrEquals();
		CompOps.add(leq);
		Function gt = intLDT.getGreaterThan();
		CompOps.add(gt);
		Function geq = intLDT.getGreaterOrEquals();
		CompOps.add(geq);
		Operator eq = Equality.EQUALS;
		CompOps.add(eq);

	}

	public void readAndRefineAntecedentPredicates(Sequent seq) {
		Semisequent ante = seq.antecedent();
		for (SequentFormula sf : ante) {
			for (Operator f : CompOps) {
				if (sf.formula().op().equals(f)) {
					delCompPred(sf);
					break;
				}
			}

			if (sf.formula().op().equals(depLDT.getRPred()) || sf.formula().op().equals(depLDT.getWPred())) {
				delDepPred(seq, sf);
			}
		}
//		System.out.println("depList size after delDepPred: " + depList.size());
		refinedCompList = compList;
		refinedDepList = depPredRefineSubSet(seq, delEmptyLocSet(seq, depList));
	}

	private void delCompPred(SequentFormula sf) {
		Term lh = sf.formula().sub(0);
//		System.out.println("LH: " + lh + " Op: " + lh.op().getClass() + " Arity: " + lh.op().arity() + " Sort: " + lh.sort());
		Term rh = sf.formula().sub(1);
//		System.out.println("RH: " + rh+ " Op: " + lh.op().getClass() + " Arity: " + lh.op().arity()+ " Sort: " + rh.sort());
		if (isProgOrLogVars(lh) && isProgOrLogVars(lh)
				&& rh.sort() != services.getTypeConverter().getBooleanType().getSort()) {
//			System.out.println("Prog or Log vars");

			Term eq = tb.equals(lh, rh);
			Term gt = tb.gt(lh, rh);
			Term geq = tb.geq(lh, rh);
			Term lt = tb.lt(lh, rh);
			Term leq = tb.leq(lh, rh);
			Set<Term> toDelete = new HashSet<Term>();

			for (Term compT : compList) {
				if (sf.formula().equals(eq) && (compT.equals(gt) || compT.equals(lt))) {
//				System.out.println(sf.formula().toString());
					toDelete.add(compT);
//					System.out.println("Comp pred " + compT + " is added to delete set.");
				} else if (sf.formula().equals(gt) && (compT.equals(lt) || compT.equals(leq) || compT.equals(eq))) {
//				System.out.println(sf.formula().toString());
					toDelete.add(compT);
//					System.out.println("Comp pred " + compT + " is added to delete set.");

				} else if (sf.formula().equals(geq) && compT.equals(lt)) {
//				System.out.println(sf.formula().toString());
					toDelete.add(compT);
//					System.out.println("Comp pred " + compT + " is added to delete set.");

				} else if (sf.formula().equals(lt) && (compT.equals(gt) || compT.equals(geq) || compT.equals(eq))) {
//				System.out.println(sf.formula().toString());
					toDelete.add(compT);
//					System.out.println("Comp pred " + compT + " is added to delete set.");

				} else if (sf.formula().equals(leq) && compT.equals(gt)) {
//				System.out.println(sf.formula().toString());
					toDelete.add(compT);

				}
			}
			compList.removeAll(toDelete);
		}
	}

	private void delDepPred(Sequent seq, SequentFormula sf) {
		Operator op = sf.formula().op();
		Term locSet = sf.formula().sub(0);
		Set<Term> toDelete = new HashSet<Term>();

		for (Term t : depList) {
			if (proofNonEmptyIntersection(seq, t.sub(0), locSet)) {
				if (op.equals(depLDT.getRPred()) && t.op().equals(depLDT.getNoR())) {
					toDelete.add(t);
				} else if (op.equals(depLDT.getWPred()) && t.op().equals(depLDT.getNoW())) {
					toDelete.add(t);
				}
			}
		}
		depList.removeAll(toDelete);

	}

	private Set<Term> depPredRefineSubSet(Sequent seq, Set<Term> dependencePredicatesSet) {
		Set<Term> toKeep = new HashSet<Term>();

		for (Term t1 : dependencePredicatesSet) {
			if (t1.op().equals(depLDT.getNoRaW()) || t1.op().equals(depLDT.getNoWaR())) {
				for (Term t2 : dependencePredicatesSet) {
					if ((t2.op().equals(depLDT.getNoR()) || t2.op().equals(depLDT.getNoW()))
							&& proofSubSet(seq, t1.sub(0), t2.sub(0))) {
						toKeep.add(t1);
					}
				}
			} else if (t1.op().equals(depLDT.getNoWaW())) {
				for (Term t2 : dependencePredicatesSet) {
					if (t2.op().equals(depLDT.getNoW()) && proofSubSet(seq, t1.sub(0), t2.sub(0))) {
						toKeep.add(t1);
					}
				}
			}

		}
//		System.out.println("toKeep size " + toKeep.size());
		dependencePredicatesSet.removeAll(toKeep);
//		System.out.println("dependencePredicatesSet size after refine by subset: " + dependencePredicatesSet.size());
		Set<Term> refined2 = depPredRefine2(seq, dependencePredicatesSet);
//		System.out.println("Refined by #2 size: " + refined2.size());
		toKeep.addAll(refined2);
//		System.out.println("Size after everything " + toKeep.size());
		return toKeep;
	}

	private Set<Term> depPredRefine2(Sequent seq, Set<Term> dependencePredicatesSet) {
		Set<Term> toDelete = new HashSet<Term>();
		Semisequent ante = seq.antecedent();
		Term formulaIntersect = null;

		for (SequentFormula sf1 : ante) {
			if (sf1.formula().op().equals(depLDT.getRPred())) {
				for (SequentFormula sf2 : ante) {
					if (sf2.formula().op().equals(depLDT.getWPred())) {
						if (proofNonEmptyIntersection(seq, sf2.formula().sub(0), sf1.formula().sub(0))) {
							formulaIntersect = tb.intersect(sf1.formula().sub(0), sf2.formula().sub(0));
							if (proofLT(seq, sf2.formula().sub(1), sf1.formula().sub(1))) {
								for (Term term : dependencePredicatesSet) {
									if (term.op().equals(depLDT.getNoRaW())
											&& proofNonEmptyIntersection(seq, term.sub(0), formulaIntersect)) {
										toDelete.add(term);
									}
								}
							} else if (proofLT(seq, sf1.formula().sub(1), sf2.formula().sub(1))) {
								for (Term term : dependencePredicatesSet) {
									if (term.op().equals(depLDT.getNoWaR())) {
										if (proofNonEmptyIntersection(seq, term.sub(0), formulaIntersect)) {
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
							&& proofNonEmptyIntersection(seq, sf2.formula().sub(0), sf1.formula().sub(0))
							&& !sf2.equals(sf1)) {
						formulaIntersect = tb.intersect(sf2.formula().sub(0), sf1.formula().sub(0));
						for (Term term : dependencePredicatesSet) {
							if (term.op().name().equals(depLDT.getNoWaW())) {
								if (proofNonEmptyIntersection(seq, term.sub(0), formulaIntersect)) {
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

	private Set<Term> delEmptyLocSet(Sequent seq, Set<Term> dependencePredicatesSet) {
		Set<Term> toDelete = new HashSet<Term>();
		for (Term term : dependencePredicatesSet) {
			if (proofEmptySet(seq, term.sub(0))) {
				toDelete.add(term);
			}
		}
		dependencePredicatesSet.removeAll(toDelete);
//		System.out.println(" dependencePredicatesSet after removing empty loc sets: " + dependencePredicatesSet.size());
		return dependencePredicatesSet;
	}

	private boolean proofEmptySet(Sequent seq, Term loc) {
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

	private boolean proofSubSet(Sequent seq, Term loc1, Term loc2) {
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

	private boolean proofLT(Sequent seq, Term ts1, Term ts2) {
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

	private boolean proofNonEmptyIntersection(Sequent seq, Term ts1, Term ts2) {
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

	protected boolean isProvable(Sequent seq, Services services) {
		final ProofStarter ps = new ProofStarter(false);
//		System.out.println("proof " + ProofSaver.printAnything(seq, services));

		final ProofEnvironment env = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());
		try {
			ps.init(seq, env, "IsInRange Proof");
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
