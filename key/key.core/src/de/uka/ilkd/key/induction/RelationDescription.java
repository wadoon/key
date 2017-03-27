package de.uka.ilkd.key.induction;

import java.security.Provider.Service;
import java.util.LinkedList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Substitution;

public class RelationDescription {

	private LinkedList<AtomicRelationDescription> atomics;
	private LinkedList<Substitution> possibleSubstitutions;
	
	public RelationDescription(Term t, Service serv) {
		ConstructorExtractor ce = new ConstructorExtractor(t);
	}

}
