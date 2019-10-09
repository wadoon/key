package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;

public class EquivalenceClosure {

    private LinkedHashSet<EquivalenceClass> closure;
    private HashMap<Term, EquivalenceClass> lookUpMap;

    public EquivalenceClosure() {
        closure = new LinkedHashSet<EquivalenceClass>();
        lookUpMap = new HashMap<Term, EquivalenceClosure.EquivalenceClass>();
    }

    public boolean contains(Term term) {
        return lookUpMap.containsKey(term);
    }

    public boolean addEquality(Term term) {
        boolean negated = false;
        if (term.op() == Junctor.NOT) {
            term = term.sub(0);
            negated = true;
        }
        assert term
        .op() == Equality.EQUALS : "Can only add equalities and negations to equivalence closures";
        return addEquality(term.sub(0), term.sub(1), negated);
    }

    public LinkedHashSet<EquivalenceClass> getEquivalenceClasses() {
        return closure;
    }

    private boolean addEquality(Term a, Term b, boolean negated) {
        // check if terms can be added
        boolean agrnd = a.freeVars().size() == 0;
        boolean bgrnd = b.freeVars().size() == 0;
        // can only have one ground term per equivalence class
        if (agrnd && bgrnd)
            return false;

        EquivalenceClass eca = lookUpMap.get(a);
        EquivalenceClass ecb = lookUpMap.get(b);

        // if classes must be combined
        if (eca != null && ecb != null) {
            // if both classes have ground terms a combination had two, that is
            // not possible
            if (eca.containsGround() && ecb.containsGround())
                return false;
            // if classes are the same, it already contains a and b
            if (eca == ecb)
                return true;
            // if eca has ground and a is ground, eca must be the ground term of
            // eca and ecb and b cannot be ground, and vice versa so its
            // possible to combine now
            closure.remove(eca);
            closure.remove(ecb);
            EquivalenceClass ecc = union(eca, ecb);
            for(Term term: ecc) {
                lookUpMap.remove(term);
                lookUpMap.put(term, ecc);
            }
            closure.add(ecc);
            return true;
        }

        // both classes do not exist. add new class
        if(eca == null && ecb == null) {
            EquivalenceClass ec = new EquivalenceClass();
            ec.add(a);
            ec.add(b);
            lookUpMap.put(a, ec);
            lookUpMap.put(b, ec);
            closure.add(ec);
            return true;
        }

        if(eca == null && ecb != null) {
            if(ecb.containsGround() && agrnd) return false;
            ecb.add(a);
            lookUpMap.put(a, ecb);
            return true;
        }
        if(ecb == null && eca != null) {
            if(eca.containsGround() && bgrnd) return false;
            eca.add(b);
            lookUpMap.put(b, eca);
            return true;
        }
        return false;
    }

    public String toString() {
        return closure.toString();
    }

    private EquivalenceClass union(EquivalenceClass eca, EquivalenceClass ecb) {
        EquivalenceClass union = new EquivalenceClass();
        for(Term term: eca) union.add(term);
        for(Term term: ecb) union.add(term);
        return union;
    }

    public class EquivalenceClass extends HashSet<Term> {

        /**
         *
         */
        private static final long serialVersionUID = 2375017123605046175L;
        private Term ground = null;

        public boolean containsGround() {
            return ground != null;
        }

        public Term getGroundTerm() {
            return ground;
        }

        public String toString() {
            return super.toString() + " ground: " + ground.toString();
        }

        @Override
        public boolean add(Term term) {
            if (term.freeVars().size() == 0) {
                assert ground == null : "overwriting ground term. this is no good";
                ground = term;
            }
            return super.add(term);
        }

        public Term first() {
            Iterator<Term> it = iterator();
            if(it.hasNext()) return it.next();
            return null;
        }



    }

}
