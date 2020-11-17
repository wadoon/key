package de.uka.ilkd.key.strategy.normalization.simple;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

import java.util.Objects;

class Literal {

    private final Term atom;
    private final boolean polarity;
    private final int hashCode;

    Literal(Term atom, boolean polarity) {
        this.atom = atom;
        this.polarity = polarity;
        this.hashCode = Objects.hash(this.atom, this.polarity);
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
        return hashCode;
    }

    @Override
    public boolean equals(Object obj) {
        if(this == obj) return true;
        if(!(obj instanceof Literal)) return false;
        Literal other = (Literal) obj;
        if(hashCode() != other.hashCode()) return false;
        return this.atom.equals(other.atom) && this.polarity == other.polarity;
    }

    @Override
    public String toString() {
        return (polarity ? "" : "!") + atom.toString();
    }
}
