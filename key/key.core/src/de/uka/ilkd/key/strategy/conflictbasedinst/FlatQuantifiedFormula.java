package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Iterator;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
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

    private Term flattenedBody;
    private LinkedHashSet<QuantifiableVariable> vars;
    private LinkedHashSet<Term> constraints;

    public FlatQuantifiedFormula(Term term,
            LinkedHashSet<QuantifiableVariable> vars, LinkedHashSet<Term> constraints) {
        super();
        this.flattenedBody = term;
        this.vars = vars;
        this.constraints = constraints;
    }

    public Term getFlattenedBody() {
        return flattenedBody;
    }

    public LinkedHashSet<QuantifiableVariable> getVars() {
        return vars;
    }

    public LinkedHashSet<Term> getConstraints() {
        return constraints;
    }

    public Term toTerm(Services services) {
        TermBuilder tb = services.getTermBuilder();
        Term ret = flattenedBody;
        ret = tb.imp(tb.and(constraints), ret);
        return concatQuantifier(ret, vars.iterator(), tb);
    }

    private Term concatQuantifier(Term ret, Iterator<QuantifiableVariable> it, TermBuilder tb) {
        QuantifiableVariable qv = it.next();
        if(it.hasNext()) {
            return tb.all(qv, concatQuantifier(ret, it, tb));
        } else {
            return tb.all(qv, ret);
        }
    }

    @Override
    public boolean equals(Object obj) {
        if(obj == this) return true;
        if(obj == null) return false;
        if(!(obj instanceof FlatQuantifiedFormula)) return false;
        FlatQuantifiedFormula fqf = (FlatQuantifiedFormula) obj;
        return fqf.getConstraints().equals(this.getConstraints())
                && fqf.getFlattenedBody().equals(this.getFlattenedBody())
                && fqf.getVars().equals(this.getVars());
    }




}
