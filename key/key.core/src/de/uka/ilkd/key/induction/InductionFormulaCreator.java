package de.uka.ilkd.key.induction;

import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.util.Pair;

public class InductionFormulaCreator {
	
	public static Term buildFormula(Term phi, Services s, RelationDescription selected){
		TermBuilder tb = s.getTermBuilder();
		Term original = phi;
		RelationDescription rd = selected;
		LinkedHashSet<QuantifiableVariable> varsToBind = new LinkedHashSet<>();
		Term inductionFormula = tb.tt();
		Term stepCases = tb.tt();
		Term originalWithoutAll;
		QuantifiableVariable inductionVariable = SchemaVariableFactory.createVariableSV(
				new Name(tb.newName(rd.getInductionVariable().sort())), 
				rd.getInductionVariable().sort()
		);
		
		if(phi.op().name().toString() == "all"){
			phi = phi.sub(0);
		}
		originalWithoutAll = phi;
		phi = tb.subst(rd.getInductionVariable(), tb.var(inductionVariable), phi);
		
		for(AtomicRelationDescription atomic : rd.getAtomics()){
			Term range = atomic.getRange();
			Term hypothesis = atomic.getHypothesis();
			
			Term stepTerm = tb.all(
				inductionVariable, 
				tb.imp(
					tb.subst(
						rd.getInductionVariable(), 
						tb.var(inductionVariable), 
						tb.and(range, hypothesis)
					), 
					phi
				)
			);
			stepCases = tb.and(stepCases, stepTerm);
				
			inductionFormula = tb.and(inductionFormula, createCaseTerm(atomic, originalWithoutAll, tb));
			varsToBind.addAll(atomic.getInductionVariables());
		}

		/*
		 * If you are familiar with the theory of Christoph Walther, you might miss the base case here.
		 * This case is included in the step cases.
		 */
		inductionFormula = stepCases;
		
		//this might be a bit overkill but currently it works
		for(QuantifiableVariable qv : inductionFormula.freeVars()){
			varsToBind.add(qv);
		}
		
		//TODO: introduce a forall statement for each variable created by the substitutions
		inductionFormula = tb.all(varsToBind, inductionFormula);
		
		//todo: (this is a hack)remove tb.or and change the taclet from replace to add.
		return tb.or(inductionFormula, original);	
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

}
