package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

public class SideProof {

	private final Services services;
	private final TermBuilder tb;
	private final Sequent seq;

	public SideProof(Services s, Sequent sequent) {
		services = s;
		tb = services.getTermBuilder();
		seq = sequent;
	}

	boolean proofSubSetWIndex(SequentFormula cIndexFormula, Term loc1, Term loc2) {
		Term fml = tb.subset(loc1, loc2);
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();
		sideSeq = sideSeq.addFormula(cIndexFormula, true, true).sequent();

		Set<Term> locSetVars = new HashSet<Term>();
		for (Term t : loc1.subs()) {
			locSetVars.addAll(collectProgramAndLogicVariables(t));
		}
		for (Term t : loc2.subs()) {
			locSetVars.addAll(collectProgramAndLogicVariables(t));
		}

		Set<Term> anteFmlVars = new HashSet<Term>();
		for (SequentFormula sfAnte : seq.antecedent()) {
			anteFmlVars = collectProgramAndLogicVariables(sfAnte.formula());
			for (Term tfv : anteFmlVars) {
				if (locSetVars.contains(tfv)) {
					sideSeq = sideSeq.addFormula(sfAnte, true, true).sequent();
					break;
				}
			}
		}

		Set<Term> succFmlVars = new HashSet<Term>();
		for (SequentFormula sfSucc : seq.succedent()) {
			succFmlVars = collectProgramAndLogicVariables(sfSucc.formula());
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

	boolean proofLT(Term ts1, Term ts2) {
		Term fml = tb.lt(ts1, ts2);
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();

		Set<Term> locSetVars = new HashSet<Term>();
		for (Term t : ts1.subs()) {
			locSetVars.addAll(collectProgramAndLogicVariables(t));
		}
		for (Term t : ts2.subs()) {
			locSetVars.addAll(collectProgramAndLogicVariables(t));
		}

		Set<Term> anteFmlVars = new HashSet<Term>();
		for (SequentFormula sfAnte : seq.antecedent()) {
			anteFmlVars = collectProgramAndLogicVariables(sfAnte.formula());
			for (Term tfv : anteFmlVars) {
				if (locSetVars.contains(tfv)) {
					sideSeq = sideSeq.addFormula(sfAnte, true, true).sequent();
					break;
				}
			}
		}

		Set<Term> succFmlVars = new HashSet<Term>();
		for (SequentFormula sfSucc : seq.succedent()) {
			succFmlVars = collectProgramAndLogicVariables(sfSucc.formula());
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

	boolean proofNonEmptyIntersectionWIndex(SequentFormula cIndexFormula, Term ts1, Term ts2) {
		Term fml_1 = tb.not(tb.equals(tb.intersect(ts1, ts2), tb.empty()));
		Set<Term> locSetVars = new HashSet<Term>();
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml_1), false, true).sequent();

		sideSeq = sideSeq.addFormula(cIndexFormula, true, true).sequent();

		for (Term t : ts1.subs())
			locSetVars.addAll(collectProgramAndLogicVariables(t));
		for (Term t : ts2.subs())
			locSetVars.addAll(collectProgramAndLogicVariables(t));

		Set<Term> anteFmlVars = new HashSet<Term>();
		for (SequentFormula sfAnte : seq.antecedent()) {
			anteFmlVars = collectProgramAndLogicVariables(sfAnte.formula());
			for (Term tfv : anteFmlVars) {
				if (locSetVars.contains(tfv)) {
					sideSeq = sideSeq.addFormula(sfAnte, true, true).sequent();
					break;
				}
			}
		}

		Set<Term> succFmlVars = new HashSet<Term>();
		for (SequentFormula sfSucc : seq.succedent()) {
			succFmlVars = collectProgramAndLogicVariables(sfSucc.formula());
			for (Term tfv : succFmlVars) {
				if (locSetVars.contains(tfv)) {
					sideSeq = sideSeq.addFormula(sfSucc, false, true).sequent();
					break;
				}
			}
		}
//		System.out.println(sideSeq);
		boolean closed = isProvable(sideSeq, services);
//		System.out.println(closed);
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

	private Set<Term> collectProgramAndLogicVariables(Term term) {

		Set<Term> res = new HashSet<Term>();
		if (!term.containsJavaBlockRecursive()) {
			if (term.op() instanceof ProgramVariable)
				res.add(term);
			else if (term.op() instanceof Function && term.sort() != Sort.FORMULA
					&& (term.arity() == 0 || term.arity() == 1) && term.freeVars().isEmpty())
				res.add(term);

			else
				for (Term sub : term.subs())
					res.addAll(collectProgramAndLogicVariables(sub));
		}
		return res;
	}
}
