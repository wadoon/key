package de.uka.ilkd.key.induction;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.util.Pair;

public class InductionFormulaCreator {
	
	public static Term buildFormula(Term t, Services s, RelationDescription selected){
		TermBuilder tb = s.getTermBuilder();
		
		if(t.op().name().toString() == "all"){
			t = t.sub(0);
		}
		RelationDescription rd = selected;
		
		Term inductionFormula = tb.not(conjunctionOfAtomicRanges(rd, s));	//base case
		LinkedList<QuantifiableVariable> varsToBind = new LinkedList<>();
		inductionFormula = tb.imp(inductionFormula, t);		
		for(AtomicRelationDescription atomic : rd.getAtomics()){
			inductionFormula = tb.and(inductionFormula, createCaseTerm(atomic, t, tb));
			varsToBind.addAll(atomic.getInductionVariables());
		}
		
		//this might be a bit overkill but currently it works
		for(QuantifiableVariable qv : inductionFormula.freeVars()){
			varsToBind.add(qv);
		}
		
		//TODO: introduce a forall statement for each variable created by the substitutions
		inductionFormula = tb.all(varsToBind, inductionFormula);//tb.imp(inductionFormula, t));
		
		
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
		LinkedList<Term> lot = new LinkedList<>();
		lot.add(t);
		lot = createSubstitutedTerms(atomic, lot, tb, t.boundVars().toImmutableList());
		lot.remove(t);
		caseTerm = tb.and(
				caseTerm, 	//TODO: test whether a recursive version of boundVars is needed here.
				tb.and(lot)
		);
		return tb.imp(caseTerm, t);
	}
	
	/**
	 * 
	 * @param atomic: an atomic relation-description
	 * @param terms: the terms which shall be substituted
	 * @param tb: a TermBuilder
	 * @param qvs: an ImmutableList of the QuantifiableVariables which shall be substituted.
	 * @return a LinkedList&lt;Term&gt; which contains all possible combinations of substitutions as a list of terms.
	 */
	private static LinkedList<Term> createSubstitutedTerms(
			AtomicRelationDescription atomic, 
			LinkedList<Term> terms, 
			TermBuilder tb, 
			ImmutableList<QuantifiableVariable> qvs
	){
		LinkedList<Term> result = new LinkedList<>();
		if(qvs.isEmpty()){	//this is the base case of the recursion
			return terms;	//it returns and 
		}
		else{	//step case (create a additional term for each substitution of each term).
			QuantifiableVariable head = qvs.head();
			List<Pair<QuantifiableVariable, Term>> substitutions = atomic.getSubstitutions();
			for(Term t : terms){
				if(t.op().name().toString() == "all"){
					t = t.sub(0);
				}
				for(Pair<QuantifiableVariable, Term> subst : substitutions){
					if(subst.first.sort() == head.sort()){
						result.add(tb.subst(head, subst.second, t));
					}
				}
			}
		
			return createSubstitutedTerms(
				atomic,
				result,
				tb,
				qvs.tail()
			);
		}
	}
	
	/**
	 * 
	 * @param rd a RelationDescription
	 * @param tb a TermBuilder
	 * @return a term which consists of the conjunction of the range-formula from the AtomicRelationDescriptions
	 * of the given RelationDescription
	 */
	private static Term conjunctionOfAtomicRanges(RelationDescription rd, Services s){
		TermBuilder tb = s.getTermBuilder();
		LinkedList<Term> ranges = new LinkedList<Term>();
		for(AtomicRelationDescription atom : rd.getAtomics()){
			ranges.add(RelationDescription.replaceTermSVwithVariableSV(atom.getRange(), s, new HashMap<TermSV, QuantifiableVariable>()));
		}
		return tb.and(ranges);
	}

}
