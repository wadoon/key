package de.uka.ilkd.key.loopinvgen;

import java.util.Set;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.operator.ComparativeOperator;
import de.uka.ilkd.key.java.expression.operator.Equals;
import de.uka.ilkd.key.java.expression.operator.GreaterOrEquals;
import de.uka.ilkd.key.java.expression.operator.GreaterThan;
import de.uka.ilkd.key.java.expression.operator.LessOrEquals;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

public class PredicateRefinement {

	public Set<Term> depList;
	public Set<ComparativeOperator> compList;
	private Semisequent ante;
	private final Goal goal;
	private final Services services;
	private final Name noRAW, noWAR, noWAW, noW, noR, rPred, wPred;
	private final TermBuilder tb;

	public PredicateRefinement(Goal g, Set<ComparativeOperator> compPredList, Set<Term> depPredList) {
		goal = g;
		services = goal.proof().getServices();
		tb = services.getTermBuilder();
		compList = compPredList;
		depList = depPredList;
		ante = goal.sequent().antecedent();// From the main proof
		noRAW = new Name("noRAW");
		noWAR = new Name("noWAR");
		noWAW = new Name("noWAW");
		noW = new Name("noW");
		noR = new Name("noR");
		rPred = new Name("rPred");
		wPred = new Name("wPred");
	}

	public void antecedentPredicate() {
		for (SequentFormula sf : ante) {
			if (sf.formula().op() instanceof ComparativeOperator) {
				delCompPred((ComparativeOperator) sf.formula().op());

			} else if (sf.formula().op().name().equals(rPred) || sf.formula().op().name().equals(wPred)) {
				delDepPred(sf);
			} else {
				// Just skip.
				System.out.println("The formula's operator in antecedent is not comparative or dependence. It is: "
						+ sf.formula().op());
			}
		}
		depPredRefine1(depList);
		depPredRefine2(ante, depList);
	}

	

	private void delCompPred(ComparativeOperator cp) {
		ExtList children = new ExtList();
		children.add((Object) cp.getChildAt(0));
		children.add((Object) cp.getChildAt(1));

		Equals eq = new Equals(children);
		GreaterThan gt = new GreaterThan(children);
		GreaterOrEquals goe = new GreaterOrEquals(children);
		LessThan lt = new LessThan(children);
		LessOrEquals loe = new LessOrEquals(children);

		if (cp instanceof Equals) {
			compList.remove(gt);
			compList.remove(lt);
		} else if (cp instanceof GreaterThan) {
			compList.remove(lt);
			compList.remove(loe);
			compList.remove(eq);
		}

		else if (cp instanceof GreaterOrEquals) {
			compList.remove(lt);
		}

		else if (cp instanceof LessThan) {
			compList.remove(gt);
			compList.remove(goe);
			compList.remove(eq);
		}

		else if (cp instanceof LessOrEquals) {
			compList.remove(gt);
		}
	}

	private void delDepPred(SequentFormula sf) {
		Name name = sf.formula().op().name();// sub(0)
		Term locSet = sf.formula().sub(1);

		for (Term t : depList) {
			if (proofSubSet(t.sub(1), locSet)) {
				if (name == rPred && t.sub(0) == noR) {
					depList.remove(t);
				} else if (name == wPred && t.sub(0) == noW) {
					depList.remove(t);
				}
			}
		}
	}

	private boolean proofSubSet(Term loc1, Term loc2) {
		Term fml = tb.subset(loc1, loc2);
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();
		// Additinal ones from main Sequent
		// seq = seq.addFormula(cf, true, true).sequent();
		boolean closed = isProvable(seq, services);
		// true: Holds, false: Unknown
		System.out.println(ProofSaver.printAnything(seq, services));// Human readable v
		return closed;
	}

	protected boolean isProvable(Sequent seq, Services services) {

		final ProofStarter ps = new ProofStarter(false);
		final ProofEnvironment env = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());
		try {
			ps.init(seq, env, "IsInRange Proof");
		} catch (ProofInputException pie) {
			pie.printStackTrace();
			return false;
		}

//        final StrategyProperties sp = setupStrategy();

//        ps.setStrategyProperties(sp);
//        ps.setMaxRuleApplications(maxRuleApps);
		// ps.setTimeout(timeoutInMillis);
		final ApplyStrategyInfo info = ps.start();

		return info.getProof().closed();
	}

	private void depPredRefine1(Set<Term> NewDepPredList) {
		for (Term t1 : NewDepPredList) {
			if (t1.sub(0) == noR) {
				for (Term t2 : NewDepPredList) {
					if ((t2.sub(0) == noRAW || t2.sub(0) == noWAR) && proofSubSet(t2.sub(1), t1.sub(1))) {
						NewDepPredList.remove(t2);
					}
				}
			}

			else if (t1.sub(0) == noW) {
				for (Term t2 : NewDepPredList) {
					if ((t2.sub(0) == noRAW || t2.sub(0) == noWAR || t2.sub(0) == noWAW)
							&& proofSubSet(t2.sub(1), t1.sub(1))) {
						NewDepPredList.remove(t2);
					}
				}
			}
		}
	}
	private void depPredRefine2(Semisequent ante2, Set<Term> depList2) {
		for (SequentFormula sf : ante2) {
			if(sf.formula().op().name().equals(rPred)) {//Add one more to cover noWAW
				for (SequentFormula sf2 : ante2) {
					if(sf2.formula().op().name().equals(wPred) && proofSubSet(sf2.formula().sub(1), sf.formula().sub(1))) {
						if(proofLT(sf2.formula().sub(2), sf.formula().sub(2))) {//Solve int problem
							for (Term term : depList2) {
								if(term.sub(0) == noWAR && proofSubSet(term.sub(1), sf2.formula().sub(1)))
									depList2.remove(term);
							}
						} else if(proofGT(sf.formula().sub(2),sf2.formula().sub(2))) {
							for (Term term : depList2) {
								if(term.sub(0) == noRAW && proofSubSet(term.sub(1), sf2.formula().sub(1)))
									depList2.remove(term);
							}
						}
							
					}
				}
			}
		}
		
	}

	private boolean proofLT(Term ts1, Term ts2) {
		Term fml = tb.lt(ts1, ts2);
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();
		// Additinal ones from main Sequent
		// seq = seq.addFormula(cf, true, true).sequent();
		boolean closed = isProvable(seq, services);
		// true: Holds, false: Unknown
		System.out.println(ProofSaver.printAnything(seq, services));// Human readable v
		return closed;
	}

	
	private boolean proofGT(Term ts1, Term ts2) {
		Term fml = tb.gt(ts1, ts2);
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();
		// Additinal ones from main Sequent
		// seq = seq.addFormula(cf, true, true).sequent();
		boolean closed = isProvable(seq, services);
		// true: Holds, false: Unknown
		System.out.println(ProofSaver.printAnything(seq, services));// Human readable v
		return closed;
	}

//	public Term predConj(Set<Term> refinedDepPreds, Set<ComparativeOperator> refinedCompPreds) {
//	Set<Term> allPreds = refinedDepPreds;
//	for (ComparativeOperator cp : refinedCompPreds) {
//		allPreds.add((Term) cp);
//	}
//	
//	return tb.and(allPreds); //basically LIG of one branch
//}



}
