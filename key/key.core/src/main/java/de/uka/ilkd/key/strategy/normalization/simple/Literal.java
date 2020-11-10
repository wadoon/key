package de.uka.ilkd.key.strategy.normalization.simple;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

class Literal {

    private final Term atom;
    private final boolean polarity;

    Literal(Term atom, boolean polarity) {
        this.atom = atom;
        this.polarity = polarity;
    }

    public boolean getPolarity() {
        return this.polarity;
    }

    public Term getAtom() {
        return this.atom;
    }

    public Term toTerm(TermBuilder builder) { return polarity ? atom : builder.not(atom);}

    @Override
    public int hashCode() {
        return super.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        return super.equals(obj);
    }

    @Override
    public String toString() {
        return (polarity ? "" : "!") + atom.toString();
    }
}
