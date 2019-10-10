package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.logic.Term;

public class ExtendedFunctionIndex {

    private HashMap<IndexTuple, Term> extFunIndex;
    private HashMap<Term, LinkedHashSet<Term>> eqMap;


    public ExtendedFunctionIndex(HashMap<Term, LinkedHashSet<Term>> eqMap) {
        this.eqMap = eqMap;
        extFunIndex = new HashMap<IndexTuple, Term>();
    }

    private ExtendedFunctionIndex(HashMap<IndexTuple, Term> extFunIndex,
            HashMap<Term, LinkedHashSet<Term>> eqMap) {
        super();
        this.extFunIndex = extFunIndex;
        this.eqMap = eqMap;
    }



    public void add(Term term) {
        extFunIndex.putIfAbsent(IndexTuple.create(term, eqMap), term);
    }

    public Collection<Term> getTerms() {
        return extFunIndex.values();
    }

    public ExtendedFunctionIndex copy(HashMap<Term, LinkedHashSet<Term>> eqMap) {
        HashMap<IndexTuple, Term> extFunIndex = new HashMap<IndexTuple, Term>();
        this.extFunIndex.forEach((key, value) -> {
            extFunIndex.put(key, value);
        });
        return new ExtendedFunctionIndex(extFunIndex, eqMap);
    }

}
