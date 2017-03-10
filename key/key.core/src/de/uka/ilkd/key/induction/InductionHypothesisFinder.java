package de.uka.ilkd.key.induction;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;

public class InductionHypothesisFinder {

	public InductionHypothesisFinder() {
		// TODO Auto-generated constructor stub
	}
	
	/**
	 * 
	 * @param allQuantifiedTerm is a term quantified by the "forall" quantifier. Note that 
	 * the "forall" quantifier is not needed for this function to work correctly. This function is 
	 * just mostly used in this context.
 	 * @return An ImmutableSet&lt;Sort&gt; the types of all variables in the given formula
	 */
	public ImmutableSet<Sort> collectSortsFromTerm(Term allQuantifiedTerm){
				
		//get all variables from the given term
		ImmutableArray<QuantifiableVariable> boundVars = allQuantifiedTerm.boundVars();
		ImmutableSet<QuantifiableVariable> variables = allQuantifiedTerm.freeVars();
		for(QuantifiableVariable bv: boundVars){
			variables.add(bv);
		}
		
		ImmutableSet<Sort> sorts
		for()
		
		
		return null;
	}

}
