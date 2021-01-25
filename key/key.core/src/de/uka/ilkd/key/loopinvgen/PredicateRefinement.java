package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

public class PredicateRefinement {

	private Set<Term> depList;
	public Set<Term> refinedDepList;
	private Set<Term> compList = new HashSet<Term>();
	public Set<Term> refinedCompList = new HashSet<Term>();
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
//		Function eq = intLDT.get
		Operator eq = Equality.EQUALS;
		CompOps.add(eq);

	}

	public void readAndRefineAntecedentPredicates(Sequent seq) {
		Semisequent ante = seq.antecedent();
		for (SequentFormula sf : ante) {
			for (Operator f : CompOps) {
				if (sf.formula().op() == f) {
//					System.out.println("comp pred spotted: " + sf);
					delCompPred(sf);
					break;
				}
			}

			if (sf.formula().op() == depLDT.getRPred() || sf.formula().op() == depLDT.getWPred()) {
//				System.out.println("Dep pred spotted: " + sf);
				delDepPred(seq, sf);
			}
		}
		refinedCompList = compList;
//		System.out.println(compList.size());
		refinedDepList = depPredRefine1(seq, depList);

	}

	private void delCompPred(SequentFormula sf) {
		Term lh = sf.formula().sub(0);
//		System.out.println("LH: " + lh + " Op: " + lh.op().getClass() + " Arity: " + lh.op().arity() + " Sort: " + lh.sort());
		Term rh = sf.formula().sub(1);
//		System.out.println("RH: " + rh+ " Op: " + lh.op().getClass() + " Arity: " + lh.op().arity()+ " Sort: " + rh.sort());
		if (isProgOrLogVars(lh) && isProgOrLogVars(lh) && rh.sort() != services.getTypeConverter().getBooleanType().getSort()) {
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
//					System.out.println("Comp pred " + compT + " is added to delete set.");

				}
			}
			compList.removeAll(toDelete);
//			System.out.println(compList.toString());
//			System.out.println(compList.size());
		}
	}

	private void delDepPred(Sequent seq, SequentFormula sf) {
		Operator op = sf.formula().op();
		Term locSet = sf.formula().sub(0);
		Set<Term> toDelete = new HashSet<Term>();

		for (Term t : depList) {
			if (proofSubSet(seq, t.sub(0), locSet)) {
				if (op == depLDT.getRPred() && t.op() == depLDT.getNoR()) {
					toDelete.add(t);
//					System.out.println("delDepPred Method: Dep pred " + t + " is going to be deleted.");
				} else if (op == depLDT.getWPred() && t.op() == depLDT.getNoW()) {
					toDelete.add(t);
//					System.out.println("delDepPred Method:  Dep pred " + t + " is going to be deleted.");
				}
			}
		}
//		System.out.println("Del by delDepPred: " + toDelete);
		depList.removeAll(toDelete);
	}

	private Set<Term> depPredRefine1(Sequent seq, Set<Term> dependencePredicatesSet) {
		Set<Term> toDelete = new HashSet<Term>();

		for (Term t1 : dependencePredicatesSet) {
			if (t1.op() == depLDT.getNoR()) {
				for (Term t2 : dependencePredicatesSet) {
					if ((t2.op()==depLDT.getNoRaW() || t2.op()== depLDT.getNoWaR())
							&& proofSubSet(seq, t2.sub(0), t1.sub(0))) {
						toDelete.add(t2);
//						System.out.println("delPredRefine1: Dep pred " + t2 + " is going to be deleted.");
					}
				}
			} else if (t1.op() == depLDT.getNoW()) {
				for (Term t2 : dependencePredicatesSet) {
					if ((t2.op() == depLDT.getNoRaW() || t2.op() == depLDT.getNoWaR() || t2.op() == depLDT.getNoWaW())
							&& proofSubSet(seq, t2.sub(0), t1.sub(0))) {
						toDelete.add(t2);
//						System.out.println("delPredRefine1: Dep pred " + t2 + " is going to be deleted.");
					}
				}
			}
		}
		Set<Term> toDelete2 = new HashSet<Term>();
		for (Term t : toDelete) {

			if (t.toString().equals("noWaR(arrayRange(a,Z(1(#)),sub(i,Z(1(#)))))")) {
				toDelete2.add(t);
				// System.out.println("_____________________________________");
			}

		}
		toDelete.removeAll(toDelete2);

//		System.out.println("Del by REFINE 1: " + toDelete);
		dependencePredicatesSet.removeAll(toDelete);
//		System.out.println("Dep Pred Set after REFINE1: " + dependencePredicatesSet);
		return depPredRefine2(seq, dependencePredicatesSet);
	}

	private Set<Term> depPredRefine2(Sequent seq, Set<Term> dependencePredicatesSet) {
		Set<Term> toDelete = new HashSet<Term>();
		Semisequent ante = seq.antecedent();

		for (SequentFormula sf1 : ante) {
			if (sf1.formula().op() == depLDT.getRPred()) {
				for (SequentFormula sf2 : ante) {
					if (sf2.formula().op() == depLDT.getWPred()) {
						proofNonEmptyIntersection(seq, sf2.formula().sub(0), sf1.formula().sub(0));
//						if (proofNonEmptyIntersection(seq, sf2.formula().sub(0), sf1.formula().sub(0))) {
//							System.out.println("Timestamps: " + sf2.formula().sub(1) + "   " + sf1.formula().sub(1));
//							if (proofLT(seq, sf2.formula().sub(1), sf1.formula().sub(1))) {
//								for (Term term : dependencePredicatesSet) {
//									if (term.op().name().equals(noRaW) && proofSubSet(seq, term.sub(0),
//											tb.intersect(sf1.formula().sub(0), sf2.formula().sub(0)))) {
//										toDelete.add(term);
//										System.out.println("Dep pred REFINE 2:" + term + " is going to be deleted.");
//									}
//								}
//							} else if (proofLT(seq, sf1.formula().sub(1), sf2.formula().sub(1))) {
//								System.out.println("Name should be noWaR and loc set should be subset of: "
//										+ tb.intersect(sf1.formula().sub(0), sf2.formula().sub(0)));
//								for (Term term : dependencePredicatesSet) {
//									if (term.op().name().equals(noWaR) && proofSubSet(seq, term.sub(0),
//											tb.intersect(sf1.formula().sub(0), sf2.formula().sub(0)))) {
//										toDelete.add(term);
//										System.out.println("Dep pred REFINE 2:" + term + " is going to be deleted.");
//									}
//								}
//							}
//
//						}
					}
				}
			} 
//			else if (sf1.formula().op().name().equals(wPred)) {
//				for (SequentFormula sf2 : ante) {
//					if (sf2.formula().op().name().equals(wPred)
//							&& proofNonEmptyIntersection(seq, sf2.formula().sub(0), sf1.formula().sub(0))
//							&& !sf2.formula().sub(1).equals(sf1.formula().sub(1))) {
//						System.out.println("Name should be noWaW and loc set should be subset of: "
//								+ tb.intersect(sf1.formula().sub(0), sf2.formula().sub(0)));
////						System.out.println(sf2.formula().sub(1) +"   WTF   "+ sf.formula().sub(1));
//						for (Term term : dependencePredicatesSet) {
//							if (term.op().name().equals(noWaW) && proofSubSet(seq, term.sub(0),
//									tb.intersect(sf1.formula().sub(0), sf2.formula().sub(0)))) {
//								toDelete.add(term);
//								System.out.println("Dep pred REFINE 2:" + term + " is going to be deleted.");
//							}
//						}
//					}
//				}
//			}
		}
		dependencePredicatesSet.removeAll(toDelete);
		return dependencePredicatesSet;
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
		// true: Holds, false: Unknown
		System.out.println(ProofSaver.printAnything(sideSeq, services));// Human readable v
//		System.out.println("This proof is closed:  " + seq);
		if (closed) {
			System.out.println(ts1 + " is LESS THAN " + ts2);
		}
		return closed;
	}

//	private boolean proofGT(Sequent seq, Term ts1, Term ts2) {
//		Term fml = tb.gt(ts1, ts2);
//		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();
//
//		Set<Term> locSetVars = new HashSet<Term>();
//		for (Term t : ts1.subs()) {
//			locSetVars.addAll(getProgAndLogVars(t));
//		}
//		for (Term t : ts2.subs()) {
//			locSetVars.addAll(getProgAndLogVars(t));
//		}
//
//		Set<Term> anteFmlVars = new HashSet<Term>();
//		for (SequentFormula sfAnte : seq.antecedent()) {
//			anteFmlVars = getProgAndLogVars(sfAnte.formula());
//			for (Term tfv : anteFmlVars) {
//				if (locSetVars.contains(tfv)) {
//					sideSeq = sideSeq.addFormula(sfAnte, true, true).sequent();
//					break;
//				}
//			}
//		}
//
//		Set<Term> succFmlVars = new HashSet<Term>();
//		for (SequentFormula sfSucc : seq.succedent()) {
//			succFmlVars = getProgAndLogVars(sfSucc.formula());
//			for (Term tfv : succFmlVars) {
//				if (locSetVars.contains(tfv)) {
//					sideSeq = sideSeq.addFormula(sfSucc, false, true).sequent();
//					break;
//				}
//			}
//		}
//
//		boolean closed = isProvable(seq, services);
////		System.out.println(ProofSaver.printAnything(seq, services));
//		if (closed) {
//			System.out.println(ts1 + " is GREATER THAN " + ts2);
//		}
//		return closed;
//	}

//	private boolean proofNEQ(Sequent seq, Term ts1, Term ts2) {
//		Term fml = tb.not(tb.equals(ts1, ts2));
//		Set<Term> locSetVars = new HashSet<Term>();
//		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();
//
//		for (Term t : ts1.subs())
//			locSetVars.addAll(getProgAndLogVars(t));
//		for (Term t : ts2.subs())
//			locSetVars.addAll(getProgAndLogVars(t));
//
//		Set<Term> anteFmlVars = new HashSet<Term>();
//		for (SequentFormula sfAnte : seq.antecedent()) {
//			anteFmlVars = getProgAndLogVars(sfAnte.formula());
//			for (Term tfv : anteFmlVars) {
//				if (locSetVars.contains(tfv)) {
//					sideSeq = sideSeq.addFormula(sfAnte, true, true).sequent();
//					break;
//				}
//			}
//		}
//
//		Set<Term> succFmlVars = new HashSet<Term>();
//		for (SequentFormula sfSucc : seq.succedent()) {
//			succFmlVars = getProgAndLogVars(sfSucc.formula());
//			for (Term tfv : succFmlVars) {
//				if (locSetVars.contains(tfv)) {
//					sideSeq = sideSeq.addFormula(sfSucc, false, true).sequent();
//					break;
//				}
//			}
//		}
//
//		boolean closed = isProvable(seq, services);
////		System.out.println(ProofSaver.printAnything(seq, services));
//
//		if (closed) {
//			System.out.println(ts1 + " is NOT EQUAL " + ts2);
//		}
//		return closed;
//	}

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
		System.out.println("Side Seq: " + sideSeq);
		boolean closed = isProvable(sideSeq, services);
		System.out.println(ProofSaver.printAnything(sideSeq, services));
		System.out.println("Side seq. res: " + closed);
		if (closed) {
			System.out.println(ts1 + " intersect with " + ts2 + " is NOT EMPTY");
		}
		return closed;
	}

	protected boolean isProvable(Sequent seq, Services services) {
		final ProofStarter ps = new ProofStarter(false);
//		System.out.println("proof " + services.getProof().toString());

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
		System.out.println("rules: "+ ps.getProof().getStatistics());
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
//				System.out.println(term.toString());
				return true;
			} else
				for (Term sub : term.subs())
					isProgOrLogVars(sub);
		}
		return false;
	}

}
