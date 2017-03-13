package de.uka.ilkd.key.induction;

import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableMap;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Substitution;

public class InductionHypothesisFinder {

	private QuantifiableVariable inductionVariable;
	private LinkedList<QuantifiableVariable> variables;
	private LinkedList<Term> terms;
	private LinkedList<Substitution> substitutions;
	
	public InductionHypothesisFinder() {
		variables = new LinkedList<QuantifiableVariable>();
		terms = new LinkedList<Term>();
		substitutions = new LinkedList<Substitution>();
		
	}
	
	/**
	 * 
	 * @param t
	 */
	public void addTerm(Term t){
		if(InductionHypothesisFinder.addIfNotContained(terms, t)){
			InductionHypothesisFinder.addAllIfNotContained(variables, InductionHypothesisFinder.collectVariablesFromTerm(t));
		}
	}
	
	/**
	 * 
	 * @param t and all its subterms will be added recursive.
	 */
	public void addTermWithAllSubterms(Term t){
		
		addTerm(t);
		
		ImmutableArray<Term> subtermArray = t.subs();
		if(subtermArray.size() > 0){
			for(Term subterm: subtermArray){
				addTermWithAllSubterms(subterm);
			}
		}
	}
	
	public void addSubstitution(Substitution subst){
		if(InductionHypothesisFinder.addIfNotContained(this.substitutions, subst)){
			InductionHypothesisFinder.addAllIfNotContained(variables, InductionHypothesisFinder.collectVariablesFromSubstitution(subst));
		}
	}
	
	/**
	 * 
	 * @param collection to which the given element is added if it does not exists in this collection.
	 * @param element which is added to the given collection
	 * @return true if the given element did not exists in the given collection (if it was added) else false (if it was not added).
	 */
	private static <T> boolean addIfNotContained(Collection<T> collection, T element){
		//for some special cases this may need a closer look!
		if(collection == null || !collection.contains(element)){	//maybe contains is not strong enough to compare to Sorts or QuantifiableVariables
			collection.add(element);
			return true;
		}
		else{
			return false;
		}
	}
	
	/**
	 * 
	 * @param collection the collection to which the elements of the given Iterable will be added.
	 * @param iterable
	 */
	private static <T> void addAllIfNotContained(Collection<T> collection, Iterable<T> iterable){
		for(T element: iterable){
			addIfNotContained(collection, element);
		}
	}
	
	/**
	 * 
	 * @return the private variable "variables" which contains all variables
	 */
	public ImmutableArray<QuantifiableVariable> getVariables(){
		return new ImmutableArray<QuantifiableVariable>(variables);
	}
	
	/**
	 * 
	 * @param allQuantifiedTerm is a term quantified by the "forall" quantifier. Note that 
	 * the "forall" quantifier is not needed for this function to work correctly. This function is 
	 * just mostly used in this context.
 	 * @return An Linked&lt;Sort&gt; the types of all variables in the given formula
	 */
	private static LinkedList<QuantifiableVariable> collectVariablesFromTerm(Term allQuantifiedTerm){
		LinkedList<QuantifiableVariable> collectedVariables = new LinkedList<QuantifiableVariable>();
		
		InductionHypothesisFinder.addIterableToList(allQuantifiedTerm.freeVars(), collectedVariables);
		InductionHypothesisFinder.addIterableToList(allQuantifiedTerm.boundVars(), collectedVariables);
				
		return collectedVariables;
	}
	
	/**
	 * 
	 * @param subst (Substitution)
	 * @return An ImmutatbleArray&lt;Sort&gt; which holds all the Sorts used in the given Substitution.
	 */
	private static LinkedList<QuantifiableVariable> collectVariablesFromSubstitution(Substitution subst){
		
		ImmutableMap<QuantifiableVariable, Term> varMap = subst.getVarMap();
		LinkedList<QuantifiableVariable> collectedVariables = new LinkedList<QuantifiableVariable>();
		
		for(Iterator<QuantifiableVariable> i = varMap.keyIterator(); i.hasNext(); ){
			QuantifiableVariable var = i.next();
			Term currentTerm;
			
			collectedVariables.add(var);
			
			currentTerm = varMap.get(var); 
			InductionHypothesisFinder.addIterableToList(currentTerm.boundVars(), collectedVariables);
			InductionHypothesisFinder.addIterableToList(currentTerm.freeVars(), collectedVariables);
			
		}
		
		return collectedVariables;
	}
	
	/**
	 * 
	 * @param iterable an Iterable of type T.
	 * @param list as any list of any type (needs to be the same type as the ImmutableArray)
	 * @return The given list with the elements of the given array added to it.
	 */
	private static <T> void addIterableToList(Iterable<T> iterable, List<T> list){
		for(T element : iterable){
			list.add(element);
		}
	}
	
	/**
	 * 
	 * @param variables is an Iterable&lt;QuantifiableVariable&gt; which holds the variables whose Sort are needed.
	 * @return An ImmutableArray&lt;Sort&gt; which holds the Sorts of the given variables. Note that this array 
	 * does not have any duplicates and is in lexicographic order.
	 */
	public ImmutableArray<Sort> getSorts(){
		LinkedList<Sort> sorts = new LinkedList<Sort>();
		for(QuantifiableVariable v: variables){
			Sort s = v.sort();
			if(!sorts.contains(s)){	//avoid duplicates
				sorts.add(s);
			}
		}
		
		//sort the Sorts in lexicographic order.
		Collections.sort(
			sorts, 
			new Comparator<Sort>(){
				@Override
				public int compare(Sort s1, Sort s2){
					String nameS1 = s1.declarationString();
					String nameS2 = s2.declarationString();
					return nameS1.compareTo(nameS2); 
				}
			}
		);
		
		return new ImmutableArray<Sort>(sorts);
	}

}
