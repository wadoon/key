package de.uka.ilkd.key.strategy.normalization;

import de.uka.ilkd.key.logic.Term;

public class Atom {

    private final Term term;

    public Atom(Term term) {
        // TODO: Test if term is atom and throw exception if not.
        this.term = term;
    }

    public Term getTerm() {
        return term;
    }

    @Override
    public int hashCode() {
        return term.hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if(o instanceof Atom) {
            Atom atom = (Atom) o;
            return term.equals(atom.term);
        }
        return term.equals(o);
    }

}
