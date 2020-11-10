package de.uka.ilkd.key.strategy.normalization.optimized;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

public class Literal {

    private static final int PRIME = 59;

    private final Term atom;
    private final boolean polarity;
    private final Literal inverse;
    private final int hashCode;

    public Literal(Term atom, boolean polarity) {
        this.atom = atom;
        this.polarity = polarity;
        this.hashCode = (PRIME + atom.hashCode()) * PRIME + (polarity ? 1 : 0);
        this.inverse = new Literal(atom, !polarity, this);
    }

    private Literal(Term atom, boolean polarity, Literal inverse) {
        this.atom = atom;
        this.polarity = polarity;
        this.inverse = inverse;
        this.hashCode = (59 + atom.hashCode()) * 59 + (polarity ? 1 : 0);
    }

    public boolean getPolarity() {
        return this.polarity;
    }

    public Term getAtom() {
        return this.atom;
    }

    public Literal inverse() {
        return this.inverse;
    }

    public Term toTerm(TermBuilder builder) { return polarity ? atom : builder.not(atom);}

    @Override
    public int hashCode() {
        return hashCode;
    }

    @Override
    public boolean equals(Object obj) {
        if(this == obj) return true;
        if(obj instanceof Literal) {
            Literal other = (Literal) obj;
            if(this.hashCode() == other.hashCode()) {
                return true;
            }else {
                if(this.getPolarity() != other.getPolarity()) return false;
                if(!this.getAtom().equals(other.getAtom())) return false;
                return true;
            }
        }
        return false;
    }

    @Override
    public String toString() {
        return (polarity ? "" : "!") + atom.toString();
    }

    private int computeHash() {
       return (PRIME + getAtom().hashCode()) * PRIME + (getPolarity() ? 1 : 0);
    }
}
