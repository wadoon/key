package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;
import java.util.Set;

import org.apache.commons.math3.util.IterationEvent;
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
import de.uka.ilkd.key.ldt.DependenciesLDT;
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
import de.uka.ilkd.key.proof.io.ProofSaver;

public class LIGNew {

	private final Sequent seq;
	private final Services services;
	private final TermBuilder tb;
	private Term low, high, index, guard;
	private Set<Term> arrays = new HashSet<>();
	private final RuleApplication ruleApp;
	private Set<Term> oldPreds = new HashSet<>();
	private Set<Term> allPreds = new HashSet<>();
	private final DependenciesLDT depLDT;
	
	public LIGNew(Services s, Sequent sequent) {
		seq = sequent;
		System.out.println(seq);
		ruleApp = new RuleApplication(s, seq);
//		services = proof.getServices();// New service after unwind
		services = ruleApp.services;
		tb = services.getTermBuilder();
		depLDT = new DependenciesLDT(services);
	}

	public void mainAlg() {
		getLow(seq);
		getIndexAndHigh(seq);
		getLocSet(seq);
		
//		System.out.println("Goals before shift: "+services.getProof().openGoals());
		ImmutableList<Goal> goalsAfterShift = ruleApp.applyShiftUpdateRule(services.getProof().openGoals());
//		System.out.println("number of goals after shift: " + goalsAfterShift.size());
//		System.out.println("Goals after shift: "+ ProofSaver.printAnything(goalsAfterShift.head().sequent(), services));
		ImmutableList<Goal> goalsAfterUnwind = null;

		Goal currentGoal = goalsAfterShift.head();
//		System.out.println(currentGoal);
//		ConstructAllCompPreds cac = new ConstructAllCompPreds(services, low, index, high);
//		allPreds.addAll(cac.cons());
		//Initial set of Comparison predicates
		allPreds.add(tb.lt(low, index));// l<i 
		allPreds.add(tb.gt(index, low));//i>l
		allPreds.add(tb.gt(index, high));// i>h 
		allPreds.add(tb.lt(high, index));//h<i
		allPreds.add(tb.gt(low, high));// l>h 
		allPreds.add(tb.lt(high, low));//h<l
		
//		allPreds.add(tb.geq(index, low));// i>=l 
//		allPreds.add(tb.leq(index, high));// i<=h 
//		allPreds.add(tb.geq(low, high));// l<=h 
		//Initial set of dependence predicates
		for (Term arr : arrays) {
			allPreds.add(tb.noR(tb.arrayRange(arr, low, high)));
			allPreds.add(tb.noW(tb.arrayRange(arr, low, high)));
//			allPreds.add(tb.noRaW(tb.arrayRange(arr, low, high)));
//			allPreds.add(tb.noWaR(tb.arrayRange(arr, low, high)));
//			allPreds.add(tb.noWaW(tb.arrayRange(arr, low, high)));
			
			allPreds.add(tb.noR(tb.arrayRange(arr, low, index)));
			allPreds.add(tb.noW(tb.arrayRange(arr, low, index)));
//			allPreds.add(tb.noRaW(tb.arrayRange(arr, low, index)));
//			allPreds.add(tb.noWaR(tb.arrayRange(arr, low, index)));
//			allPreds.add(tb.noWaW(tb.arrayRange(arr, low, index)));
			
			allPreds.add(tb.noR(tb.arrayRange(arr, index, high)));
			allPreds.add(tb.noW(tb.arrayRange(arr, index, high)));
//			allPreds.add(tb.noRaW(tb.arrayRange(arr, index, high)));
//			allPreds.add(tb.noWaR(tb.arrayRange(arr, index, high)));
//			allPreds.add(tb.noWaW(tb.arrayRange(arr, index, high)));
		}

		System.out.println("Initial Predicate Set: ");
		for (Term term : allPreds) {
			System.out.println(term);
		}
		PredicateRefinementNew pr0 = new PredicateRefinementNew(services, currentGoal.sequent(), allPreds, index);
		allPreds=pr0.predicateCheckAndRefine();
//		System.out.println(ProofSaver.printAnything(seq, services));
		int itrNumber = 0;
		do {
			oldPreds.removeAll(oldPreds);
			oldPreds.addAll(allPreds);

			goalsAfterUnwind = ruleApp.applyUnwindRule(goalsAfterShift);
			goalsAfterShift = ruleApp.applyShiftUpdateRule(goalsAfterUnwind);
			System.out.println("Goal After Shift: " + goalsAfterShift);
			
			currentGoal = ruleApp.findLoopUnwindTacletGoal(goalsAfterShift);
//			currentIndexFormula = currentIndexEq(currentGoal.sequent(), index);
			PredicateRefinementNew pr = new PredicateRefinementNew(services, currentGoal.sequent(), allPreds, index);
			allPreds=pr.predicateCheckAndRefine();
			itrNumber ++;
			
		} while (allPreds.size() != oldPreds.size() && itrNumber <10);
		
		
		
		System.out.println("===========Terminated===========");
		System.out.println("Number of iterations: " + itrNumber);
		System.out.println("LIG is the conjunction of: ");
		for (Term term : allPreds) {
			System.out.println(term);
		}
		System.out.println(" of size " + allPreds.size());
		
		PredicateListCompressionNew plcNew = new PredicateListCompressionNew(services, currentGoal.sequent(), allPreds, false);

		allPreds = plcNew.compression();
		System.out.println("Compressed LIG is the conjunction of: ");
		for (Term term : allPreds) {
			System.out.println(term);
		}
		System.out.println(" of size " + allPreds.size());
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

	void getLoopGuard(Sequent seq) {
		Term guard = null;
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
					if (expr instanceof GreaterOrEquals) {
						guard = tb.geq(expr2term(((ComparativeOperator) expr).getExpressionAt(0)),
								expr2term(((ComparativeOperator) expr).getExpressionAt(1)));
					} else if (expr instanceof GreaterThan) {
						guard = tb.gt(expr2term(((ComparativeOperator) expr).getExpressionAt(0)),
								expr2term(((ComparativeOperator) expr).getExpressionAt(1)));
					} else if (expr instanceof LessOrEquals) {
						guard = tb.leq(expr2term(((ComparativeOperator) expr).getExpressionAt(0)),
								expr2term(((ComparativeOperator) expr).getExpressionAt(1)));
					} else if (expr instanceof LessThan) {
						guard = tb.lt(expr2term(((ComparativeOperator) expr).getExpressionAt(0)),
								expr2term(((ComparativeOperator) expr).getExpressionAt(1)));
					}

				}
				break;
			}
		}
		this.guard = guard;
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
