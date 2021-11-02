//package de.uka.ilkd.key.loopinvgen;
//
//import java.util.HashSet;
//import java.util.Set;
//
//import org.key_project.util.collection.ImmutableList;
//
//import de.uka.ilkd.key.java.Expression;
//import de.uka.ilkd.key.java.ProgramElement;
//import de.uka.ilkd.key.java.Services;
//import de.uka.ilkd.key.java.Statement;
//import de.uka.ilkd.key.java.expression.operator.ComparativeOperator;
//import de.uka.ilkd.key.java.expression.operator.GreaterOrEquals;
//import de.uka.ilkd.key.java.expression.operator.GreaterThan;
//import de.uka.ilkd.key.java.expression.operator.LessOrEquals;
//import de.uka.ilkd.key.java.expression.operator.LessThan;
//import de.uka.ilkd.key.java.statement.While;
//import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
//import de.uka.ilkd.key.logic.ProgramPrefix;
//import de.uka.ilkd.key.logic.Sequent;
//import de.uka.ilkd.key.logic.SequentFormula;
//import de.uka.ilkd.key.logic.Term;
//import de.uka.ilkd.key.logic.TermBuilder;
//import de.uka.ilkd.key.logic.op.ElementaryUpdate;
//import de.uka.ilkd.key.logic.op.Equality;
//import de.uka.ilkd.key.logic.op.LocationVariable;
//import de.uka.ilkd.key.logic.op.Modality;
//import de.uka.ilkd.key.logic.op.UpdateApplication;
//import de.uka.ilkd.key.logic.op.UpdateJunctor;
//import de.uka.ilkd.key.logic.sort.ArraySort;
//import de.uka.ilkd.key.pp.Notation.ParallelUpdateNotation;
//import de.uka.ilkd.key.proof.Goal;
//
//public class LIGMultipleArrayMultipleIndex {
//
//	private final Sequent seq;
//	private final Services services;
//	private final TermBuilder tb;
//	private Term index;
//	private Set<Term> arrays = new HashSet<>();
//	private Set<ArrayIndexData> arrayDataTable = new HashSet<>();
//	
//	
//	private final RuleApplication ruleApp;
//	private Set<Term> oldCompPred = new HashSet<>();
//	private Set<Term> oldDepPred = new HashSet<>();
//
//	public LIGMultipleArrayMultipleIndex(Services s, Sequent sequent) {
//		seq = sequent;
//		ruleApp = new RuleApplication(s, seq);
////		services = proof.getServices();// New service after unwind
//		services = ruleApp.services;
//		tb = services.getTermBuilder();
//
//	}
//
//	public void mainAlg() {
//		getLow(seq);
//		getIndexesAndHighs(seq);
//		getArraysAndIndexes(seq);
//		
//		ImmutableList<Goal> goalsAfterShift = ruleApp.applyShiftUpdateRule(services.getProof().openGoals());
//		ImmutableList<Goal> goalsAfterUnwind = null;
//		
//		Goal currentGoal = goalsAfterShift.head();
//		SequentFormula currentIndexFormula = null;
//		
//		Set<Term> allCompPreds = new HashSet<>();
//		Set<Term> allDepPreds = new HashSet<>();
//		
//		for(ArrayIndexData ad :arrayDataTable) {
//			ConstructAllCompPreds cac = new ConstructAllCompPreds(services, ad.lowerbound, ad.index, ad.upperBound);
//			allCompPreds.addAll(cac.cons());
//			ConstructAllDepPreds cad = new ConstructAllDepPreds(services, ad.array, ad.lowerbound, ad.index, ad.upperBound);
//			allDepPreds.addAll(cad.cons());
//		}
//
//		do {
//			oldCompPred.removeAll(oldCompPred);
//			oldCompPred.addAll(allCompPreds);
//			oldDepPred.removeAll(oldDepPred);
//			oldDepPred.addAll(allDepPreds);
//
////			System.out.println("NEW: " + depPreds);
////			System.out.println("OLD: " + oldDepPred);
//			currentIndexFormula = currentIndexEq(currentGoal.sequent(), index);
//
//			goalsAfterUnwind = ruleApp.applyUnwindRule(goalsAfterShift);
//			goalsAfterShift = ruleApp.applyShiftUpdateRule(goalsAfterUnwind);
//			currentGoal = ruleApp.findLoopUnwindTacletGoal(goalsAfterShift);
//
//			PredicateRefinement pr = new PredicateRefinement(services, currentGoal.sequent(), allCompPreds, allDepPreds,
//					currentIndexFormula);
//			pr.readAndRefineAntecedentPredicates();
//
//			allCompPreds = pr.refinedCompList;
//			allDepPreds = pr.refinedDepList;
////			System.out.println("DP: " + depPreds);
//
//		} while (!allCompPreds.equals(oldCompPred) || !allDepPreds.equals(oldDepPred));
//		PredicateListCompression plc = new PredicateListCompression(services, currentGoal.sequent(), currentIndexFormula);
//		//Compression is not mandetory
//		plc.compression(allDepPreds, allCompPreds);
//		System.out.println("LIG is the conjunction of: " + allCompPreds + "  size " + allCompPreds.size() + " and " + allDepPreds
//				+ " of size " + allDepPreds.size());
//	}
//
//	private SequentFormula currentIndexEq(Sequent seq2, Term index2) {
//		for (SequentFormula sf : seq2.antecedent()) {
//			Term formula = sf.formula();
//			if (formula.op() instanceof Equality) {
//				Term current_i = formula.sub(0);
//				if (current_i.equals(index2)) {
////					System.out.println("i's formula: " + sf);
//					return sf;
//				}
//			}
//		}
//		return null;
//	}
//
//	void getLow(Sequent seq) {
//		for (SequentFormula sf : seq.succedent()) {
//			Term formula = sf.formula();
//			if (formula.op() instanceof UpdateApplication) {
//				Term update = UpdateApplication.getUpdate(formula);
//				lows.add(getLowsHelper(update));
//			}
//		}
//	}
//	
//	private Term getLowsHelper(Term upd) {
//		Term low = null;
//		if (upd.op() instanceof ElementaryUpdate) {
//			low =upd.sub(0);
//		}
//		else if(upd.op() == UpdateJunctor.PARALLEL_UPDATE) {
//			getLowsHelper(upd.sub(0));
//			getLowsHelper(upd.sub(1));
//		}
//		return low;
//	}
//
//	void getIndexesAndHighs(Sequent seq) {
//		Expression high = null, index = null;
//		for (SequentFormula sf : seq.succedent()) {
//			Term formula = skipUpdates(sf.formula());
//			if (formula.op() == Modality.DIA) {
//				ProgramElement pe = formula.javaBlock().program();
//				Statement activePE;
//				if (pe instanceof ProgramPrefix) {
//					activePE = (Statement) ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
//				} else {
//					activePE = (Statement) pe.getFirstElement();
//				}
//				if (activePE instanceof While) {
//					Expression expr = (Expression) ((While) activePE).getGuardExpression();
//					if (expr instanceof GreaterOrEquals || expr instanceof GreaterThan) {
//						high = ((ComparativeOperator) expr).getExpressionAt(0);
//						index = ((ComparativeOperator) expr).getExpressionAt(1);
//					} else if (expr instanceof LessOrEquals || expr instanceof LessThan) {
//						high = ((ComparativeOperator) expr).getExpressionAt(1);
//						index = ((ComparativeOperator) expr).getExpressionAt(0);
//					}
//				}
//				break;
//			}
//		}
//		this.high = expr2term(high);
//		this.index = expr2term(index);
//	}
//
//	private void getIndexesAndHighsHelper(Expression expr) {
//		if (expr instanceof GreaterOrEquals || expr instanceof GreaterThan) {
//			high = ((ComparativeOperator) expr).getExpressionAt(0);
//			index = ((ComparativeOperator) expr).getExpressionAt(1);
//		} else if (expr instanceof LessOrEquals || expr instanceof LessThan) {
//			high = ((ComparativeOperator) expr).getExpressionAt(1);
//			index = ((ComparativeOperator) expr).getExpressionAt(0);
//		}
//		
//	}
//	Term expr2term(Expression expr) {
//		return this.services.getTypeConverter().convertToLogicElement(expr);
//	}
//
//	private Term skipUpdates(Term formula) {
//		return formula.op() instanceof UpdateApplication ? UpdateApplication.getTarget(formula) : formula;
//	}
//
//	
//
//	void getArraysAndIndexes(Sequent seq) {
//		for (SequentFormula sf : seq.succedent()) {
//			Term formula = skipUpdates(sf.formula());
//			if (formula.op() == Modality.DIA) {
//				Statement activePE = (Statement) formula.javaBlock().program();
//				Set<LocationVariable> lvs = extractProgramVariable(activePE);
//				findArray(lvs);
//			}
//		}
//	}
//	
//	Set<LocationVariable> extractProgramVariable(Statement s) {
//		ProgramVariableCollector pvc = new ProgramVariableCollector(s, services);
//		pvc.start();
//		return pvc.result();
//	}
//	
//	private void findArray(Set<LocationVariable> set) {
//		for (LocationVariable v : set) {
//			if (v.sort() instanceof ArraySort) {
//				// System.out.println(v + " is an array with element sort " + ((ArraySort)
//				// v.sort()).elementSort());
//				// KeYJavaType kjt = v.getKeYJavaType(services);
//				// kjt.getSort(); // logic sort
//				// kjt.getJavaType(); // Java type
//				// System.out.println(v + " is of KeY sort " + kjt.getSort());
//				// System.out.println(v + " is of java type " + kjt.getJavaType());
//				
//				arrays.add(tb.var(v));
//			}
//		}
//	}
//
//	
//	void newHelper() {
//		//indexBounds = Term[arrays.size()][3];
//		
//	}
//}
