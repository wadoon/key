package de.uka.ilkd.key.strategy.conflictbasedinst;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;



public class Constraint {

    private Term var;
    private Term term;
    private Term constraint;
    private TermBuilder tb;

    public Constraint(Term var, Term term, TermBuilder tb) {
        this.var = var;
        this.term = term;
        this.tb = tb;
    }

    public Term getTerm() {
        return term;
    }

    public Term getVar() {
        return var;
    }

    public Term getConstraint() {
        if(constraint == null) {
            constraint = tb.equals(var, term);
        }
        return constraint;
    }

    public String toString() {
        return getConstraint().toString();
    }

}
