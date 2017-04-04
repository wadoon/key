package de.uka.ilkd.key.induction;

import java.util.Collection;
import java.util.LinkedList;
import java.util.Set;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.abstraction.Variable;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Substitution;
import de.uka.ilkd.key.util.Pair;

public class AtomicRelationDescription {
	
	/** a quantifier-free formula 
	 * needed: 
	 *  - access to all variables of the formula
	 *  - the formula need to be a boolean
	 * */
	private Term rangeFormula;	//make sure that term is the right class to handle the range formula
	
	/** TODO: find fitting description. 
	 * this should not be empty */
	private LinkedList<Pair<QuantifiableVariable, Term>> domainSubstitution;
	
	public AtomicRelationDescription(Term range, LinkedList<Pair<QuantifiableVariable, Term>> substitions){
		rangeFormula = range;
		domainSubstitution = substitions;
	}
	
	/**
	 * 
	 * @return Set&lt;Variable&gt;: all variables used in rangeFormula and/or domainSubstitution.
	 */
	public LinkedList<QuantifiableVariable> getRelevantVariables(){
		LinkedList<QuantifiableVariable> relevantVars = null;	//Find the most useful type of set
		
		addTermVars(relevantVars, rangeFormula);
		
		for(Pair<QuantifiableVariable, Term> subst : this.domainSubstitution){
			addIfNotContains(relevantVars, subst.first);
			addTermVars(relevantVars, subst.second);
		}
		
		return relevantVars;
	}
	
	private <T> void addIfNotContains(LinkedList<T> list, T element){
		if(!list.contains(element)){
			list.add(element);
		}
	}
	
	/**
	 * 
	 * @param list a list of QuantifiableVariables
	 * @param t the term whose variables should be added to the given list.
	 */
	private void addTermVars(LinkedList<QuantifiableVariable> list, Term t){
		ImmutableSet<QuantifiableVariable> freeVarsOfRangeFormula = t.freeVars();	//transform into variables
		ImmutableArray<QuantifiableVariable> boundVarsOfRangeFormula = t.boundVars();	//transform into variables
		
		for(QuantifiableVariable qv : freeVarsOfRangeFormula){
			addIfNotContains(list, qv);
		}
		
		for(QuantifiableVariable qv : boundVarsOfRangeFormula){
			addIfNotContains(list, qv);
		}
	}
	
	/**
	 * @see getRelevantVariables
	 * @return Set&lt;Varaible&gt;: all relevant variables which occur in an element of domainSubstitution.
	 */
	public Set<Variable> getInductionVariables(){
		//TODO: implementation
		// build the intersection of the variables from the range formula and the substitution.
		return null;
	}
	
	/**
	 * @return the rangeformula of this AtomicRelationDescription as Term.
	 */
	public Term getRange(){
		return this.rangeFormula;
	}	
}
