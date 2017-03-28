package de.uka.ilkd.key.induction;

import java.util.LinkedList;

import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Substitution;

public class RelationDescription {

	private LinkedList<AtomicRelationDescription> atomics;
	private LinkedList<Substitution> possibleSubstitutions;
	
	public RelationDescription(Term t, Services serv) {
		ConstructorExtractor ce = new ConstructorExtractor(t, serv);
		ImmutableArray<Function> constructors = ce.getConstructors();
		for(Function f : constructors){
			possibleSubstitutions.add(createSubstitution(f, serv));
		}
		
	}
	
	private static Substitution createSubstitution(Function f, Services s){
		//How to create a Substitution and new QuantifiableVariables.
		//TODO: return a substitution with a new QuantifiableVariable and the function with new variables as term.
		return null;
	}
	

}
