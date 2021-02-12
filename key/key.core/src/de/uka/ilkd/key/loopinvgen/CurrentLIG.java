package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;
import java.util.Set;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.expression.operator.ComparativeOperator;
import de.uka.ilkd.key.java.expression.operator.GreaterOrEquals;
import de.uka.ilkd.key.java.expression.operator.GreaterThan;
import de.uka.ilkd.key.java.expression.operator.LessOrEquals;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.proof.Goal;
import jdk.nashorn.internal.ir.annotations.Immutable;

public class CurrentLIG {

	private final Sequent seq;
	private final Services services;
	private final TermBuilder tb;
	private Term low, high, index;
	private Term array;
	private final RuleApplication ruleApp;
	public CurrentLIG(Services s, Sequent sequent) {
		seq = sequent;
		ruleApp = new RuleApplication(s, seq);
//		services = proof.getServices();// New service after unwind
		services = ruleApp.services;
		tb = services.getTermBuilder();
	}

	public void mainAlg() {
		getLow(seq);
		getIndexAndHigh(seq);
		getLocSet(seq);

		ConstructAllCompPreds cac = new ConstructAllCompPreds(services, low, index, high);
		Set<Term> compPreds = cac.cons();
		ConstructAllDepPreds cad = new ConstructAllDepPreds(services, array, low, index, high);
		Set<Term> depPreds = cad.cons();

		Set<Term> oldCompPred = new HashSet<>();
		Set<Term> oldDepPred = new HashSet<>();
		oldCompPred.addAll(compPreds);
		oldDepPred.addAll(depPreds);

//		applyShiftRule(proof.openGoals().head());
		ImmutableList<Goal> goalsAfterShift =ruleApp.applyShiftUpdateRule(services.getProof().openGoals());
		ImmutableList<Goal> goalsAfterUnwind = null;
		Goal currentGoal = null;
		int i =0;
		do {
			i++;
			goalsAfterUnwind = ruleApp.applyUnwindRule(goalsAfterShift);
			goalsAfterShift = ruleApp.applyShiftUpdateRule(goalsAfterUnwind);
			currentGoal = ruleApp.findLoopUnwindTacletGoal(goalsAfterShift);
//			pr.readAndRefineAntecedentPredicates();
//			compPreds = pr.refinedCompList;
//			depPreds = pr.refinedDepList;
//			System.out.println("Seq: "+ g.sequent());
			PredicateRefinement pr = new PredicateRefinement(services, currentGoal.sequent(), compPreds, depPreds);
			pr.readAndRefineAntecedentPredicates();
//			System.out.println("Fixed point hasn't reached.");
			oldCompPred.removeAll(oldCompPred);
//			System.out.println(oldCompPred);
			oldCompPred.addAll(compPreds);
//			System.out.println(oldCompPred);
			
			oldDepPred.removeAll(oldDepPred);
			oldDepPred.addAll(depPreds);
		} while (!compPreds.equals(oldCompPred) || !depPreds.equals(oldDepPred) || i< 3);
		System.out.println("LIG is the conjunction of: " + compPreds + "  size " + compPreds.size() + " and "
				+ depPreds + " of size " + depPreds.size());
	}

	
	void getLow(Sequent seq) {
		for (SequentFormula sf : seq.succedent()) {
			Term formula = sf.formula();
			if (formula.op() instanceof UpdateApplication) {
				Term update = UpdateApplication.getUpdate(formula);
				if (update.op() instanceof ElementaryUpdate) {
					this.low = update.sub(0);
					break;
				}
			}
		}
	}

	void getIndexAndHigh(Sequent seq) {
		Expression high = null, index = null;
		for (SequentFormula sf : seq.succedent()) {
			Term formula = skipUpdates(sf.formula());
			if (formula.op() == Modality.DIA) {
				ProgramElement pe = formula.javaBlock().program();
				Statement activePE;
				if (pe instanceof ProgramPrefix) {
					activePE = (Statement) ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
				} else {
					activePE = (Statement) pe.getFirstElement();
				}
				if (activePE instanceof While) {
					Expression expr = (Expression) ((While) activePE).getGuardExpression();
					if (expr instanceof GreaterOrEquals || expr instanceof GreaterThan) {
						high = ((ComparativeOperator) expr).getExpressionAt(0);
						index = ((ComparativeOperator) expr).getExpressionAt(1);
					} else if (expr instanceof LessOrEquals || expr instanceof LessThan) {
						high = ((ComparativeOperator) expr).getExpressionAt(1);
						index = ((ComparativeOperator) expr).getExpressionAt(0);
					}
				}
				break;
			}
		}
		this.high = expr2term(high);
		this.index = expr2term(index);
	}

	Term expr2term(Expression expr) {
		return this.services.getTypeConverter().convertToLogicElement(expr);
	}
	
	private Term skipUpdates(Term formula) {
		return formula.op() instanceof UpdateApplication ? UpdateApplication.getTarget(formula) : formula;
	}

	Set<LocationVariable> extractProgramVariable(Statement s) {
		ProgramVariableCollector pvc = new ProgramVariableCollector(s, services);
		pvc.start();
		return pvc.result();
	}

	void getLocSet(Sequent seq) {
		// How to find the targeted location set (the array)?
		for (SequentFormula sf : seq.succedent()) {
			Term formula = skipUpdates(sf.formula());
			if (formula.op() == Modality.DIA) {
				Statement activePE = (Statement) formula.javaBlock().program();
				Set<LocationVariable> lvs = extractProgramVariable(activePE);
				findArray(lvs);
			}
		}
	}
	
	private void findArray(Set<LocationVariable> set) {
		for (LocationVariable v : set) {
			if (v.sort() instanceof ArraySort) {
				// System.out.println(v + " is an array with element sort " + ((ArraySort)
				// v.sort()).elementSort());
				// KeYJavaType kjt = v.getKeYJavaType(services);
				// kjt.getSort(); // logic sort
				// kjt.getJavaType(); // Java type
				// System.out.println(v + " is of KeY sort " + kjt.getSort());
				// System.out.println(v + " is of java type " + kjt.getJavaType());
				array = tb.var(v);
			}
		}
	}

}
