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
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.proof.Goal;

public class LIGMultipleArrays {

	private final Sequent seq;
	private final Services services;
	private final TermBuilder tb;
	private Term low, high, index;
	private Set<Term> arrays = new HashSet<>();
	private final RuleApplication ruleApp;
	private Set<Term> oldCompPred = new HashSet<>();
	private Set<Term> oldDepPred = new HashSet<>();

	public LIGMultipleArrays(Services s, Sequent sequent) {
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
		
		ImmutableList<Goal> goalsAfterShift = ruleApp.applyShiftUpdateRule(services.getProof().openGoals());
		ImmutableList<Goal> goalsAfterUnwind = null;
		
		Goal currentGoal = goalsAfterShift.head();
		SequentFormula currentIndexFormula = null;
		
		ConstructAllCompPreds cac = new ConstructAllCompPreds(services, low, index, high);
		Set<Term> compPreds = cac.cons();

		Set<Term> depPreds = new HashSet<>();
		for(Term arr:arrays) {
			ConstructAllDepPreds cad = new ConstructAllDepPreds(services, arr, low, index, high);
			depPreds.addAll(cad.cons());
		}

		do {
			oldCompPred.removeAll(oldCompPred);
			oldCompPred.addAll(compPreds);
			oldDepPred.removeAll(oldDepPred);
			oldDepPred.addAll(depPreds);

//			System.out.println("NEW: " + depPreds);
//			System.out.println("OLD: " + oldDepPred);
			currentIndexFormula = currentIndexEq(currentGoal.sequent(), index);

			goalsAfterUnwind = ruleApp.applyUnwindRule(goalsAfterShift);
			goalsAfterShift = ruleApp.applyShiftUpdateRule(goalsAfterUnwind);
			currentGoal = ruleApp.findLoopUnwindTacletGoal(goalsAfterShift);

			PredicateRefinement pr = new PredicateRefinement(services, currentGoal.sequent(), compPreds, depPreds,
					currentIndexFormula);
			pr.readAndRefineAntecedentPredicates();

			compPreds = pr.refinedCompList;
			depPreds = pr.refinedDepList;
//			System.out.println("DP: " + depPreds);

		} while (!compPreds.equals(oldCompPred) || !depPreds.equals(oldDepPred));
		PredicateListCompression plc = new PredicateListCompression(services, currentGoal.sequent(), currentIndexFormula);
		//Compression is not mandetory
		plc.compression(depPreds, compPreds);
		System.out.println("LIG is the conjunction of: " + compPreds + "  size " + compPreds.size() + " and " + depPreds
				+ " of size " + depPreds.size());
	}

	private SequentFormula currentIndexEq(Sequent seq2, Term index2) {
		for (SequentFormula sf : seq2.antecedent()) {
			Term formula = sf.formula();
			if (formula.op() instanceof Equality) {
				Term current_i = formula.sub(0);
				if (current_i.equals(index2)) {
//					System.out.println("i's formula: " + sf);
					return sf;
				}
			}
		}
		return null;
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
		ProgramVariableCollectorWithArrayIndices pvc = new ProgramVariableCollectorWithArrayIndices(s, services);
		pvc.start();
//		System.out.println(pvc.result());
//		System.out.println("my array: " + pvc.array());
//		System.out.println(pvc.index());
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
//				System.out.println("old array: " + v);
				arrays.add(tb.var(v));
			}
		}
	}

}
