package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;

import java.util.HashSet;
import java.util.Set;

import org.stringtemplate.v4.compiler.STParser.expr_return;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.expression.operator.ComparativeOperator;
import de.uka.ilkd.key.java.expression.operator.GreaterOrEquals;
import de.uka.ilkd.key.java.expression.operator.GreaterThan;
import de.uka.ilkd.key.java.expression.operator.LessOrEquals;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.java.statement.IGuard;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;

public class CurrentLIG {

	private final Sequent seq;
	private final Services services;
	private final TermBuilder tb;
	private Term low, high, index;
	private Term array;
	private Set<Term> compPreds = null, depPreds = null, newCompPreds = null, newDepPreds = null;

	public CurrentLIG(Services s, Sequent seq) {
		services = s;
		tb = services.getTermBuilder();
		this.seq = seq;

	}

	public void mainAlg() {
		getLow(seq);
		getIndexAndHigh(seq);
		getLocSet(seq);

		ConstructAllCompPreds cac = new ConstructAllCompPreds(services, low, index, high);
		Set<Term> compPreds = cac.cons();
		System.out.println("Comp Preds size: " + compPreds.size());
		ConstructAllDepPreds cad = new ConstructAllDepPreds(services, array, low, index, high);
		Set<Term> depPreds = cad.cons();
		/*
		 * first unwind then shift
		 */
		mainAlg2(seq, compPreds, depPreds);
	}

	private void mainAlg2(Sequent seq, Set<Term> compPreds, Set<Term> depPreds) {
		Set<Term> oldCompPred = new HashSet<>();
		Set<Term> oldDepPred = new HashSet<>();
		
		oldCompPred.addAll(compPreds);
		oldDepPred.addAll(depPreds);
		
		PredicateRefinement pr = new PredicateRefinement(services, seq, compPreds, depPreds);
		pr.readAndRefineAntecedentPredicates();
		
		Set<Term> newCompPreds = pr.refinedCompList;
//		System.out.println("New Comp Preds size: " + newCompPreds.size());
//		System.out.println("New Comp Preds: " + newCompPreds);
		Set<Term> newDepPreds = pr.refinedDepList;
//		System.out.println("New Dep Preds: " + newDepPreds);

//		if (newCompPreds.equals(compPreds) && newDepPreds.equals(depPreds)) {
//			System.out.println(
//					"Loop Inv. is the conjunction of: " + newCompPreds + " and " + newDepPreds);
//			System.out.println("Number of LI predicates: " + newCompPreds.size() + " plus " + newDepPreds.size());
//		} else {
//			compPreds = newCompPreds;
//			depPreds = newDepPreds;
//			System.out.println(compPreds.size() + " plus "+ depPreds.size());
//			System.out.println("again");
//			mainAlg2(newSeq);
//		}
		// Testing the Comp Preds
		if (newCompPreds.equals(oldCompPred) && newDepPreds.equals(oldDepPred)) {
			System.out.println("LIG is the conjunction of: "+ newCompPreds + " of size " + newCompPreds.size() + " and " + newDepPreds + " of size " + newDepPreds.size() );
		} else {
			oldCompPred.removeAll(oldCompPred);
			oldCompPred.addAll(newCompPreds);
			
			oldDepPred.removeAll(oldDepPred);
			oldDepPred.addAll(newDepPreds);
			
			System.out.println("Fixed point hasn't reached.");
			mainAlg2(seq, newCompPreds, depPreds);
		}

	}

//	private Term fixedPoint(Services s, Sequent seq, Set<Term> oldComp, Set<Term> newComp, Set<Term> oldDep,
//			Set<Term> newDep) {
//		Term loopInv = null;
//		if (oldComp.equals(newComp) && oldDep.equals(newDep)) {
//			loopInv = tb.and(tb.and(newComp), tb.and(newDep));
//		} else {
//			oldComp = newComp;
//			oldDep = newDep;
//			PredicateRefinement pr = new PredicateRefinement(services, seq, oldComp, oldDep);
//			newComp = pr.refinedCompList;
//
//		}
//
//		return loopInv;
//	}

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

	Term expr2term(Expression expr) {
		return this.services.getTypeConverter().convertToLogicElement(expr);
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

	private Term skipUpdates(Term formula) {
		return formula.op() instanceof UpdateApplication ? UpdateApplication.getTarget(formula) : formula;
	}

	Set<LocationVariable> extractProgramVariable(Statement s) {
		ProgramVariableCollector pvc = new ProgramVariableCollector(s, services);
		pvc.start();
		return pvc.result();
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

	// only for tests
	Term low() {
		return this.low;
	}

	Term high() {
		return this.high;
	}

	Term index() {
		return this.index;
	}

//	void setValue(final Set<Term> val)
//    {
//        compPreds = newCompPreds;
//        newCompPreds    = val;
//    }
//
//    Set<Term> get()
//    {
//        return (newCompPreds);
//    }
//
//    Set<Term> getOld()
//    {
//        return (compPreds);
//    }
	
}
