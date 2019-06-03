package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.LinkedHashSet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/**
 * The flat form of a quantified formula is an equivalent quantified formula in
 * which all non-ground atoms are replaced by a fresh variable.
 *
 * <p>The flat form consists of the quantified variable, the matching constraints,
 * that is a conjunction of the equations that assign the fresh variables to the
 * replaced non-ground atoms and the flattened body, that is the original
 * quantified body where all non-ground atoms are replaced by fresh variables.
 *
 * @author Andre Challier <andre.challier@stud.tu-darmstadt.de>
 *
 */
class FlatQuantifiedFormula {

    private Term term;
    private LinkedHashSet<QuantifiableVariable> vars;
    private LinkedHashSet<Term> constraints;
    private boolean ground;

    public FlatQuantifiedFormula(Term term,
            LinkedHashSet<QuantifiableVariable> vars, LinkedHashSet<Term> constraints,
            boolean ground) {
        super();
        this.term = term;
        this.vars = vars;
        this.constraints = constraints;
        this.ground = ground;
    }

    public Term getTerm() {
        return term;
    }

    public LinkedHashSet<QuantifiableVariable> getVars() {
        return vars;
    }

    public LinkedHashSet<Term> getConstraints() {
        return constraints;
    }

    public boolean isGround() {
        return ground;
    }

    public void setGround(boolean ground) {
        this.ground = ground;
    }




}
