package de.uka.ilkd.key.strategy.conflictbasedinst.normalization;

import java.util.Objects;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Junctor;

public class Literal {

    private final Term term;
    private final boolean polarity;

    private Literal(Term term, boolean polarity) {
        if(term.op() == Junctor.NOT) {
            term = term.sub(0);
            polarity = !polarity;
        }
        this.term = term;
        this.polarity = polarity;
    }

    private Literal(Term term) {
        this(term.op() == Junctor.NOT ? term.sub(0): term, term.op() != Junctor.NOT);
    }

    public static Literal fromTerm(Term term, boolean polarity) {
        return new Literal(term, polarity);
    }

    public static Literal fromTerm(Term a) {
        return new Literal(a);
    }

    public Literal complement() {
        return new Literal(term, !polarity);
    }

    @Override
    public int hashCode() {
        return Objects.hash(term, polarity);
    }

    @Override
    public boolean equals(Object obj) {
        if(obj == this) return true;
        if(!(obj instanceof Literal)) return false;
        Literal lit = (Literal) obj;
        return this.term.equals(lit.term) && this.polarity == lit.polarity;
    }



    @Override
    public String toString() {
        String ret = term.toString();
        return polarity ? ret : "!(" + ret + ")";
    }

    public Term toTerm(TermBuilder tb) {
        return polarity ? term : tb.not(term);
    }

    public Term getTerm() {
        return term;
    }

    public boolean getPolarity() {
        return polarity;
    }
}
