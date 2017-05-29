package de.uka.ilkd.key.induction;

import java.util.LinkedList;
import java.util.List;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.util.Pair;

public class AtomicRelationDescription {
	
	private static final String COUNTER_NAME = "AtomicVariablenames";
	
	/** a quantifier-free formula 
	 * needed: 
	 *  - access to all variables of the formula
	 *  - the formula need to be a boolean
	 * */
	private Term rangeFormula;	//make sure that term is the right class to handle the range formula
	
	/** TODO: find fitting description. 
	 * this should not be empty */
	private LinkedList<Pair<QuantifiableVariable, Term>> domainSubstitution;
	
	private LinkedList<QuantifiableVariable> vars;
	
	public AtomicRelationDescription(
			Term range, 
			ImmutableArray<Function> constructors, 
			LinkedList<Pair<QuantifiableVariable, Term>> substitutions,
			Services serv
	){
		vars = new LinkedList<>();
		rangeFormula = range;		
		
		for(Function f : constructors){
			substitutions.add(createSubstitutionForFunction(f, serv));
		}
		
		domainSubstitution = substitutions;
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
	
	public List<Pair<QuantifiableVariable, Term>> getSubstitutions(){
		return this.domainSubstitution;
	}
	
	/**
	 * 
	 * @param list
	 * @param element this element is added to the given list if the list does not already contain it.
	 */
	private <T> void addIfNotContains(LinkedList<T> list, T element){
		if(!list.contains(element)){
			list.add(element);
		}
	}
	
	/**
	 * 
	 * @param f a Function
	 * @param s the Services (they are required to get the TermBuilder)
	 * @return a Pair&lt;QuantifiableVariable, Term&gt; which holds the Term consisting of the given function
	 * and new QuantifiableVariables as parameters and a new QuantifiableVariable.
	 * (maybe this QuantifiableVariable should not be part of the return value. It might be that
	 * this substitution has to be created for each existing QuantifiableVariable which has the same
	 * type 
	 */
	private Pair<QuantifiableVariable, Term> createSubstitutionForFunction(Function f, Services s){
		QuantifiableVariable result = SchemaVariableFactory.createVariableSV(generateName(f, s, "res"), f.sort());
		QuantifiableVariable[] parameters = new QuantifiableVariable[f.arity()];
		TermBuilder tb = s.getTermBuilder();
		for(int i = 0; i < f.arity(); i++){
			parameters[i] = SchemaVariableFactory.createVariableSV(generateName(f, s, "arg" + i), f.argSort(i));
			vars.add(parameters[i]);
		}
		
		//vars.add(result);
		
		return new Pair<QuantifiableVariable, Term>(
				result, 
				tb.func(f, varsToTerm(parameters, tb), new ImmutableArray<QuantifiableVariable>())
		);
	}
	

	/**
	 * 
	 * @param qvs
	 * @param tb
	 * @return the terms which only consist of the given variables.
	 */
	private static Term[] varsToTerm(QuantifiableVariable[] qvs, TermBuilder tb){
		Term[] terms = new Term[qvs.length];
		for(int i = 0; i < qvs.length; i++){
			terms[i] = tb.var(qvs[i]);
		}
		return terms;
	}

	/**
	 * 
	 * @param f a function
	 * @param s the Services (might needed later)
	 * @param suffix a String
	 * @return a new Name with a String which starts with the given Functions name then the given 
	 * suffix and the private variable varCounter. All separated by the char "_". varCounter is 
	 * increased by one for each call of this function to ensure the uniqueness of the names.
	 */
	private static Name generateName(Function f, Services s, String suffix){
		//TODO: better name generation maybe by existing code.
		//
		StringBuilder sb = new StringBuilder();
		sb.append(f.name().toString());
		sb.append("_");
		sb.append(suffix);
		sb.append("_");
		sb.append(s.getCounter(COUNTER_NAME).getCountPlusPlus());
		return new Name(sb.toString());
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
	 * @return Set&lt;Variable&gt;: all relevant variables which occur in an element of domainSubstitution.
	 */
	public LinkedList<QuantifiableVariable> getInductionVariables(){
		//TODO: build the intersection of the variables from the range formula and the substitution.
		return vars;
	}
	
	/**
	 * @return the rangeformula of this AtomicRelationDescription as Term.
	 */
	public Term getRange(){
		return this.rangeFormula;
	}
	
	/**
	 * 
	 */
	@Override
	public String toString(){
		StringBuilder sb = new StringBuilder();
		boolean firstElement = true;
		sb.append("Range Formula:");
		sb.append(this.rangeFormula.toString());
		sb.append(", Substitutions: ");
		if(this.domainSubstitution != null){
			for(Pair<QuantifiableVariable, Term> subst : this.domainSubstitution){
				if(!firstElement){
					sb.append(", ");
				}
				else{
					firstElement = false;
				}
				sb.append("{");
				sb.append(subst.first.toString());
				sb.append("\\");
				sb.append(subst.second.toString());
				sb.append("}");
			}
		}
		else{
			sb.append("no substitution found.");
		}
		return sb.toString();
	}
}
