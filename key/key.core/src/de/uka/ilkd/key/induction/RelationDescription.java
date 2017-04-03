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
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Substitution;
import de.uka.ilkd.key.util.Pair;

public class RelationDescription {

	private LinkedList<AtomicRelationDescription> atomics;
	private LinkedList<Pair<QuantifiableVariable, Term>> possibleSubstitutions;
	
	public RelationDescription(Term t, Services serv){
		ConstructorExtractor ce = new ConstructorExtractor(t, serv);
		ImmutableArray<Function> constructors = ce.getConstructors();
		LinkedList<Term> rangeFormulas;
		for(Function f : constructors){
			possibleSubstitutions.add(createSubstitutions(f, serv));
		}
		rangeFormulas = createRangeFormulas(t, serv);
	}
	
	private static LinkedList<Term> createRangeFormulas(Term t, Services s){
		ImmutableList<Named> namedrules = s.getNamespaces().ruleSets().elements();
		LinkedList<FindTaclet> rules = new LinkedList<FindTaclet>();
		//TODO: check for optimizations
		for(Named n : namedrules){
			Rule r = (Rule)n;
			if(r instanceof FindTaclet){
				FindTaclet ft = (FindTaclet)r;
				if(findTacletMatches(ft, t, s)){
					rules.add(ft);
				}
			}
		}
		//TODO: compute the range formula
		return null;
	}
	
	private static boolean findTacletMatches(FindTaclet ft, Term t, Services s){
		//TODO: return whether the given term fits to the findtaclet or not.
		MatchConditions mc = new MatchConditions();
		mc = ft.getMatcher().matchFind(t, mc, s);
		return mc != null;
	}
	
	private static LinkedList<Pair<QuantifiableVariable, Term>> createSubstitutions(Function f, Services s){
		//How to create a Substitution and new QuantifiableVariables.
		//TODO: return a substitution with a new QuantifiableVariable and the function with new variables as term.
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
