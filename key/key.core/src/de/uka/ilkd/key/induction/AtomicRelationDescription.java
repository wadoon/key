package de.uka.ilkd.key.induction;

import java.util.Collection;
import java.util.Set;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.abstraction.Variable;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Substitution;

public class AtomicRelationDescription {
	
	/** a quantifier-free formula 
	 * needed: 
	 *  - access to all variables of the formula
	 *  - the formula need to be a boolean
	 * */
	private Term rangeFormula;	//make sure that term is the right class to handle the range formula
	
	/** TODO: find fitting description. 
	 * this should not be empty */
	private Set<Substitution> domainSubstitution;	//use linkedhashset or immutableset to generate the same proof for the same problem.
	//use single substitution pair<variable, term>
	
	public AtomicRelationDescription(){
		//TODO: generate the range formula and the set of substitutions
	}
	
	/**
	 * 
	 * @return Set&lt;Variable&gt;: all variables used in rangeFormula and/or domainSubstitution.
	 */
	public Set<Variable> getRelevantVariables(){
		//TODO: collect the variables from rangeFormula and domainSubstitution
		Set<Variable> relevantVars = null;	//Find the most useful type of set
		
		ImmutableSet<QuantifiableVariable> freeVarsOfRangeFormula = rangeFormula.freeVars();	//transform into variables
		ImmutableArray<QuantifiableVariable> boundVarsOfRangeFormula = rangeFormula.boundVars();	//transform into variables
		
		for(Substitution substitution: domainSubstitution){
			ImmutableMap<QuantifiableVariable, Term> freeVarsOfSubstitution = substitution.getVarMap();	//transform into variables
		}
		
		//TODO collect the variables and add them to the set of relevant variables.
		return relevantVars;
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
	 * 
	 */
	//TODO: replace void with a returntype for "Relation"
	public void getRange(){
		
	}
	
}
