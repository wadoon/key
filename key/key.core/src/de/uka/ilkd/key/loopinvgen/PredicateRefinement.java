package de.uka.ilkd.key.loopinvgen;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Variable;
import de.uka.ilkd.key.java.expression.operator.ComparativeOperator;
import de.uka.ilkd.key.java.expression.operator.Equals;
import de.uka.ilkd.key.java.expression.operator.GreaterOrEquals;
import de.uka.ilkd.key.java.expression.operator.GreaterThan;
import de.uka.ilkd.key.java.expression.operator.LessOrEquals;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

public class PredicateRefinement {

	public Set<Term> refinedDepList;

	private Set<Term> depList;
	private Set<Term> refinedDepList0 = new HashSet<>();
	private Set<Term> refinedDepList1 = new HashSet<>();
	public Set<Term> compList  = new HashSet<Term>();
	private Semisequent ante;
	private final Services services;
	private final Name noRAW, noWAR, noWAW, noW, noR, rPred, wPred;
	private final TermBuilder tb;
	private final IntegerLDT intLDT;
	private final Set<Operator> CompOps = new HashSet<>();

	public PredicateRefinement(Services s, Sequent seq, Set<Term> compPredList, Set<Term> depPredList) {
		services = s;
		tb = services.getTermBuilder();
		compList = compPredList;
		
		depList = depPredList;
//		ante = seq.antecedent();// From the main proof
		noRAW = new Name("noRAW");
		noWAR = new Name("noWAR");
		noWAW = new Name("noWAW");
		noW = new Name("noW");
		noR = new Name("noR");
		rPred = new Name("rPred");
		wPred = new Name("wPred");

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
				if (sf.formula().op().equals(f)) {
					delCompPred(sf);
				}
			}
			
			if (sf.formula().op().name().equals(rPred) || sf.formula().op().name().equals(wPred)) {
				delDepPred(seq, sf);
			} else {
				return;
			}
		}
		System.out.println(compList.size());
		
		depPredRefine1(seq, refinedDepList0);
		depPredRefine2(seq, refinedDepList1);
	}

	private void delCompPred(SequentFormula sf) {
		Term lh = sf.formula().sub(0);
		Term rh = sf.formula().sub(1);

		Term eq = tb.equals(lh, rh);
		Term gt = tb.gt(lh, rh);
		Term geq = tb.geq(lh, rh);
		Term lt = tb.lt(lh, rh);
		Term leq = tb.leq(lh, rh);
		Set<Term> toDelete = new HashSet<Term>();
		
		for (Term compT : compList) {
			if (sf.formula().equals(eq) && (compT.equals(gt) || compT.equals(lt))) {
				System.out.println(sf.formula().toString());
				toDelete.add(compT);
				System.out.println("Comp pred " + compT + " is added to delete set.");
			}
			else if(sf.formula().equals(gt) && (compT.equals(lt) || compT.equals(leq) || compT.equals(eq))){
				System.out.println(sf.formula().toString());
				toDelete.add(compT);
				System.out.println("Comp pred " + compT + " is added to delete set.");

			}
			else if(sf.formula().equals(geq) && compT.equals(lt)) {
				System.out.println(sf.formula().toString());
				toDelete.add(compT);
				System.out.println("Comp pred " + compT + " is added to delete set.");

			}
			else if(sf.formula().equals(lt) && (compT.equals(gt) || compT.equals(geq) || compT.equals(eq))) {
				System.out.println(sf.formula().toString());
				toDelete.add(compT);
				System.out.println("Comp pred " + compT + " is added to delete set.");

			}
			else if(sf.formula().equals(leq) && compT.equals(gt)) {
				System.out.println(sf.formula().toString());
				toDelete.add(compT);
				System.out.println("Comp pred " + compT + " is added to delete set.");

			}
		}
		compList.removeAll(toDelete);
		System.out.println(compList.toString());
		System.out.println(compList.size());
		
	}

	private void delDepPred(Sequent seq, SequentFormula sf) {
		Name name = sf.formula().op().name();// sub(0)
		Term locSet = sf.formula().sub(0);

		for (Term t : depList) {
			if (proofSubSet(seq, t.sub(0), locSet)) {
				if (name == rPred && t.op().name() == noR) {
					return;
				} else if (name == wPred && t.sub(0) == noW) {
//					System.out.println();
					return;
				} else {
					refinedDepList0.add(t);
					System.out.println("Dep pred " + t + " is added.");
				}
//			} else {
//				refinedDepList0.add(t);
			}
		}
	}

	private boolean proofSubSet(Sequent seq, Term loc1, Term loc2) {
		Term fml = tb.subset(loc1, loc2);
		// System.out.println("proof sub set: " + fml.toString());
		System.out.println("Orig Seq: " + ProofSaver.printAnything(seq, services));
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();

		Set<Term> locSetVars = new HashSet<Term>();
		for (Term t : loc1.subs()) {
			locSetVars.addAll(getProgAndLogVars(t));
		}
		for (Term t : loc2.subs()) {
			locSetVars.addAll(getProgAndLogVars(t));
		}
		System.out.println("Loc Set Vars: " + locSetVars);

		Set<Term> anteFmlVars = new HashSet<Term>();
		for (SequentFormula sfAnte : seq.antecedent()) {
			anteFmlVars = getProgAndLogVars(sfAnte.formula());
			for (Term tfv : anteFmlVars) {
				if (locSetVars.contains(tfv)) {
					sideSeq = sideSeq.addFormula(sfAnte, true, true).sequent();
					System.out.println("Added to ante: " + sfAnte);
					break;
				}
			}
		}

		System.out.println("Ante Vars: " + anteFmlVars);

		Set<Term> succFmlVars = new HashSet<Term>();
		for (SequentFormula sfSucc : seq.succedent()) {
			succFmlVars = getProgAndLogVars(sfSucc.formula());
			for (Term tfv : succFmlVars) {
				if (locSetVars.contains(tfv)) {
					sideSeq = sideSeq.addFormula(sfSucc, false, true).sequent();
					System.out.println("Added to succ: " + sfSucc);
					break;
				}
			}
		}

		System.out.println("Succ Vars: " + succFmlVars);
		System.out.println("Side Seq: " + sideSeq);
		// Additinal ones from main Sequent
		// seq = seq.addFormula(cf, true, true).sequent();
		boolean closed = isProvable(sideSeq, services);
		// true: Holds, false: Unknown
		System.out.println("Subset proof" + ProofSaver.printAnything(sideSeq, services));// Human readable v
		return closed;
	}

	protected boolean isProvable(Sequent seq, Services services) {

		final ProofStarter ps = new ProofStarter(false);
//		System.out.println("proof "+ services.getProof().toString());

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

	private void depPredRefine1(Sequent seq, Set<Term> NewDepPredList) {
		for (Term t1 : NewDepPredList) {
			if (t1.sub(0) == noR) {
				for (Term t2 : NewDepPredList) {
					if ((t2.sub(0) == noRAW || t2.sub(0) == noWAR) && proofSubSet(seq, t2.sub(1), t1.sub(1))) {
						return;
//						NewDepPredList.remove(t2);
//						System.out.println(t2.toString() + " is removed");
					} else {
						refinedDepList1.add(t2);
					}
				}
			}

			else if (t1.sub(0) == noW) {
				for (Term t2 : NewDepPredList) {
					if ((t2.sub(0) == noRAW || t2.sub(0) == noWAR || t2.sub(0) == noWAW)
							&& proofSubSet(seq, t2.sub(1), t1.sub(1))) {
						return;
//						NewDepPredList.remove(t2);
//						System.out.println(t2.toString() + " is removed");
					} else {
						refinedDepList1.add(t2);
					}
				}
			} else
				refinedDepList1.add(t1);
		}
	}

	private void depPredRefine2(Sequent seq, Set<Term> depList2) {
		Semisequent ante2 = seq.antecedent();
		for (SequentFormula sf : ante2) {
			if (sf.formula().op().name().equals(rPred)) {
				for (SequentFormula sf2 : ante2) {
					if (sf2.formula().op().name().equals(wPred)
							&& proofSubSet(seq, sf2.formula().sub(1), sf.formula().sub(1))) {
						if (proofLT(sf2.formula().sub(2), sf.formula().sub(2))) {
							for (Term term : depList2) {
								if (term.sub(0) == noWAR && proofSubSet(seq, term.sub(1), sf2.formula().sub(1))) {
									return;
//									depList2.remove(term);
//									System.out.println(term.toString() + " is removed");
								} else {
									refinedDepList.add(term);
								}
							}
						} else if (proofGT(sf.formula().sub(2), sf2.formula().sub(2))) {
							for (Term term : depList2) {
								if (term.sub(0) == noRAW && proofSubSet(seq, term.sub(1), sf2.formula().sub(1))) {
									return;
//									depList2.remove(term);
//									System.out.println(term.toString() + " is removed");
								} else {
									refinedDepList.add(term);
								}
							}
						}
					}
				}
			} else if (sf.formula().op().name().equals(wPred)) {
				for (SequentFormula sf2 : ante2) {
					if (sf2.formula().op().name().equals(wPred)
							&& proofSubSet(seq, sf2.formula().sub(1), sf.formula().sub(1))) {
						if (proofNEQ(sf2.formula().sub(2), sf.formula().sub(2))) {
							for (Term term : depList2) {
								if (term.sub(0) == noWAW && proofSubSet(seq, term.sub(1), sf2.formula().sub(1))) {
									return;
//									depList2.remove(term);
//									System.out.println(term.toString() + " is removed");
								} else {
									refinedDepList.add(term);
								}
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
//		System.out.println(ProofSaver.printAnything(seq, services));// Human readable v
		return closed;
	}

	private boolean proofGT(Term ts1, Term ts2) {
		Term fml = tb.gt(ts1, ts2);
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();
		boolean closed = isProvable(seq, services);
//		System.out.println(ProofSaver.printAnything(seq, services));
		return closed;
	}

	private boolean proofNEQ(Term sub, Term sub2) {
		Term fml = tb.not(tb.equals(sub, sub2));
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();
		boolean closed = isProvable(seq, services);
//		System.out.println(ProofSaver.printAnything(seq, services));
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

	Term expr2term(Expression expr) {// Does it work here?
		return this.services.getTypeConverter().convertToLogicElement(expr);
	}

	private Set<Term> getProgAndLogVars(Term term) {

		Set<Term> res = new HashSet<Term>();
		if (!term.containsJavaBlockRecursive()) {
			if (term.op() instanceof ProgramVariable)
				res.add(term);
			else if (term.op() instanceof Function && (term.sort() != Sort.FORMULA) && term.arity() == 0)
				res.add(term);

			else
				for (Term sub : term.subs())
					res.addAll(getProgAndLogVars(sub));
		}
		return res;
	}
}
