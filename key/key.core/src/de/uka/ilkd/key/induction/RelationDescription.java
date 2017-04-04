package de.uka.ilkd.key.induction;

import java.util.LinkedList;

import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Substitution;
import de.uka.ilkd.key.util.Pair;

public class RelationDescription {

	private LinkedList<AtomicRelationDescription> atomics;
	private LinkedList<Pair<QuantifiableVariable, Term>> possibleSubstitutions;
	private LinkedList<Term> possibleRangeFormulas;
	
	
	public RelationDescription(Term t, Services serv){
		ConstructorExtractor ce = new ConstructorExtractor(t, serv);
		ImmutableArray<Function> constructors = ce.getConstructors();
		for(Function f : constructors){
			possibleSubstitutions.addAll(createSubstitutions(f, serv));
		}
		possibleRangeFormulas = createRangeFormulas(t, serv);
		
		//TODO: generate AtomicRelationDescription for all possibleRangeFormulas
		for(Term range : possibleRangeFormulas){
			/*
			 * How to select the right substitutions? Is another ConstructorExctractor needed?
			 * If yes is the one above needed?
			 */
			atomics.add(new AtomicRelationDescription(
					range,
					possibleSubstitutions	//TODO: filter this list.
					));
		}
	}
	
	public LinkedList<AtomicRelationDescription> getAtomics(){
		return this.atomics;
	}
	
	private static LinkedList<Term> createRangeFormulas(Term t, Services s){
		ImmutableList<Named> namedrules = s.getNamespaces().ruleSets().elements();
		LinkedList<Term> possibleRangeFormulas = new LinkedList<Term>();
		TermBuilder tb = s.getTermBuilder();
		//TODO:[optional] check for optimizations
		for(Named n : namedrules){
			Rule r = (Rule)n;
			if(r instanceof FindTaclet){
				FindTaclet ft = (FindTaclet)r;
				//check whether the find term of the the FindTaclet is an instance of the given term
				Term rangeFormula = createRangeFormula(t, ft.find(), s);
				//TODO:[optional] find a way to express multiple rangeformulas in one (optimization)
				/*
				 * E.g. if there are rangeformulas int x: x = 0, x = 1, x = 2
				 * make a new rangeformula x >= 0 && x <= 2 and throw the others away.
				 */
				
				//TODO:[optional] check for optimization
				int nos = rangeFormula.subs().size();
				boolean falseIsDirectSubterm = false;
				for(int i = 0; i < nos; i++){
					if(rangeFormula.sub(i).equals(tb.ff())){
						falseIsDirectSubterm = true;	//does the "and" operator work with this?
						break;							//@see createRangeFormula
					}
				}
				if(!falseIsDirectSubterm){
					possibleRangeFormulas.add(rangeFormula);
				}
			}
		}
		return possibleRangeFormulas;
	}
	
	/**
	 * 
	 * @param term
	 * @param findTerm
	 * @return if the findTerm is an instance of the given term this function returns a term which shows under 
	 * which condition the term would be the same as the findTerm. E.g. term = f(a), findTerm = f(g(x)) this function
	 * would return a = g(x). 
	 */
	private static Term createRangeFormula(Term term, Term findTerm, Services s){
		TermBuilder tb = s.getTermBuilder();
		
		if(findTerm.op() == term.op()){
			if(term.arity() > 0){
				LinkedList<Term> subterms = new LinkedList<Term>();
				for(int i = 0; i < term.arity(); i++){
					subterms.add(createRangeFormula(term.sub(i), findTerm.sub(i), s));
				}
				return tb.and(subterms);	//how does add work? two parameters or more?
			}
			else{
				//TODO:[optional] Maybe check arity for negative values and their handling
				return tb.equals(term, findTerm);
			}
		}
		else{
			return tb.ff();
		}
	}
	
	/**
	 * 
	 * @param f: a constructor
	 * @param s
	 * @return a LinkedList&lt;Pair&lt;QuantifiableVariable, Term&gt;&gt; which contains constructor substitutions
	 */
	private static LinkedList<Pair<QuantifiableVariable, Term>> createSubstitutions(Function f, Services s){
		Sort returnSort = f.sort();
		Namespace vars = s.getNamespaces().variables();
		TermBuilder tb = s.getTermBuilder();
		Term t = tb.func(f);
		LinkedList<Pair<QuantifiableVariable, Term>> substitutions = new LinkedList<Pair<QuantifiableVariable, Term>>();
		QuantifiableVariable qv = null;
		for(Named n : vars.elements()){
			if(n instanceof QuantifiableVariable){
				qv = (QuantifiableVariable)n;
				if(qv.sort().equals(returnSort)){
					substitutions.add(new Pair<QuantifiableVariable, Term>(qv, t));
				}
			}
		}
		
		return substitutions;
	}
	
}
