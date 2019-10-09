package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;

public class FunctionIndex {

    private LinkedHashMap<LinkedList<LinkedHashSet<Term>>, Term> index;
    private HashMap<Term, LinkedHashSet<Term>> eqMap;
    private HashMap<Operator, Term> funMap;

    public FunctionIndex(HashMap<Term, LinkedHashSet<Term>> eqMap, HashMap<Operator, Term> funMap) {
        this.eqMap = eqMap;
        this.funMap = funMap;
        this.index = new LinkedHashMap<LinkedList<LinkedHashSet<Term>>, Term>();
    }

    public void add(Term term) {
        Term representant = funMap.get(term.op());
        if(representant == null) return;
        index.putIfAbsent(getArgClasses(representant), representant);
    }

    public Term get(Term term) {
        return index.get(getArgClasses(term));
    }

    private LinkedList<LinkedHashSet<Term>> getArgClasses(Term term) {
        LinkedList<LinkedHashSet<Term>> argClasses = new LinkedList<LinkedHashSet<Term>>();
        for(Term sub : term.subs()) {
            argClasses.add(eqMap.computeIfAbsent(sub, set -> new LinkedHashSet<Term>(Arrays.asList(sub))));
        }
        return argClasses;
    }

}
