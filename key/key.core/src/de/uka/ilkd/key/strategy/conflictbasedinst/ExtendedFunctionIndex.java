package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Objects;

import de.uka.ilkd.key.logic.Term;

public class ExtendedFunctionIndex {

    private HashMap<IndexTuple, Term> extFunIndex;
    private HashMap<Term, LinkedHashSet<Term>> eqMap;


    public ExtendedFunctionIndex(HashMap<Term, LinkedHashSet<Term>> eqMap) {
        this.eqMap = eqMap;
        extFunIndex = new HashMap<IndexTuple, Term>();
    }

    public void add(Term term) {
        extFunIndex.putIfAbsent(IndexTuple.create(term, eqMap), term);
    }

    public Collection<Term> getTerms() {
        return extFunIndex.values();
    }

    private static class IndexTuple {

        private final LinkedHashSet<Term> funEqClass;
        private final LinkedList<LinkedHashSet<Term>> argEqClasses;
        private boolean hashset;
        private int hash;

        private IndexTuple(LinkedHashSet<Term> funEqClass, LinkedList<LinkedHashSet<Term>> argEqClasses) {
            this.funEqClass = funEqClass;
            this.argEqClasses = argEqClasses;
            hashset = false;
            hash = 0;
        }

        public static IndexTuple create(Term term, HashMap<Term, LinkedHashSet<Term>> eqMap) {
            LinkedHashSet<Term> funEqClass = eqMap.computeIfAbsent(term, set -> new LinkedHashSet<Term>(Arrays.asList(term)));
            LinkedList<LinkedHashSet<Term>> argEqClass = getArgClasses(term, eqMap);
            return new IndexTuple(funEqClass, argEqClass);
        }

        private static LinkedList<LinkedHashSet<Term>> getArgClasses(Term term, HashMap<Term, LinkedHashSet<Term>> eqMap) {
            LinkedList<LinkedHashSet<Term>> argClasses = new LinkedList<LinkedHashSet<Term>>();
            for(Term sub : term.subs()) {
                argClasses.add(eqMap.computeIfAbsent(sub, set -> new LinkedHashSet<Term>(Arrays.asList(sub))));
            }
            return argClasses;
        }


        @Override
        public int hashCode() {
            if(!hashset) {
                hash = Objects.hash(funEqClass, argEqClasses);
                hashset = true;
            }
            return hash;
        }

        @Override
        public boolean equals(Object obj) {
            if(obj == this) return true;
            if(!(obj instanceof IndexTuple)) return false;
            IndexTuple it = (IndexTuple) obj;
            return this.hashCode() == it.hashCode();
        }


    }

}
