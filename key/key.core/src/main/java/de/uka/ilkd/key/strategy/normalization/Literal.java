package de.uka.ilkd.key.strategy.normalization;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * A literal is either an atom or an atom preceded by a negation sign.
 */
public class Literal {

    private final Term atom;
    private final boolean polarity;

    public Literal(Term atom, boolean polarity) {
        this.atom = atom;
        this.polarity = polarity;
    }

    public Literal complement() {
        return new Literal(atom, !polarity);
    }

    public boolean isPositive() {
        return this.polarity;
    }

    public Term getAtom() {
        return this.atom;
    }

    public Term toTerm(TermBuilder termBuilder) {
        return polarity ? atom : termBuilder.not(atom);
    }
}
