package de.uka.ilkd.key.induction;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.operator.adt.AllObjects;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.util.Pair;

public class InductionFormulaCreator {
	
	public static Term buildFormula(Term t, Services s){
		TermBuilder tb = s.getTermBuilder();
		if(t.op() instanceof AllObjects){
			t = t.sub(1);
		}
		RelationDescription rd = select(RelationDescriptionGenerator.generate(t, s));
		Term inductionFormula = tb.not(conjunctionOfAtomicRanges(rd, tb));
		LinkedList<QuantifiableVariable> varsToBind = new LinkedList<>();
		inductionFormula = tb.imp(inductionFormula, t);
		for(AtomicRelationDescription atomic : rd.getAtomics()){
			inductionFormula = tb.and(inductionFormula, createCaseTerm(atomic, t, tb));
			varsToBind.addAll(atomic.getInductionVariables());
		}
		
		
		//TODO: introduce a forall statement for each variable created by the substitutions
		inductionFormula = tb.all(varsToBind, inductionFormula);
		
		
		//System.out.println("Bound Vars: " + inductionFormula.boundVars());
		//System.out.println("Free Vars: " + inductionFormula.freeVars());
		System.out.println("\n\nINDUCTIONFORMULA:" + inductionFormula + "\n\n");
		
		return inductionFormula;
	}
	
	/**
	 * 
	 * @param atomic
	 * @param t
	 * @param tb
	 * @return the step-case term for the given term
	 */
	private static Term createCaseTerm(AtomicRelationDescription atomic, Term t, TermBuilder tb) {
		Term caseTerm = atomic.getRange();
		
		for(Pair<QuantifiableVariable, Term> subst : atomic.getSubstitutions()){
			caseTerm = tb.and(tb.subst(subst.first, subst.second, t));
		}
		return tb.imp(caseTerm, t);
	}

	/**
	 * 
	 * @param rd a RelationDescription
	 * @param tb a TermBuilder
	 * @return a term which consists of the conjunction of the range-formula from the AtomicRelationDescriptions
	 * of the given RelationDescription
	 */
	private static Term conjunctionOfAtomicRanges(RelationDescription rd, TermBuilder tb){
		LinkedList<Term> ranges = new LinkedList<Term>();
		for(AtomicRelationDescription atom : rd.getAtomics()){
			ranges.add(atom.getRange());
		}
		return tb.and(ranges);
	}
	
	/**
	 * 
	 * @param list: a list of RelationDescription's
	 * @return one RelationDescription from the list (currently the first but this will be change in the future)
	 * TODO: improve the selection algorithm
	 */
	private static RelationDescription select(List<RelationDescription> list){
		return list.get(1);
	}
	
	

}
