package de.uka.ilkd.key.strategy.conflictbasedinst;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Quantifier;

/**
 * A Flat Form of a Quantified Formula is an equivalent formula that is build for simplification of the falsify method
 * in CBInstantiation.
 * <p>
 * For a given quantified formula \forall x0: ... \forall xn: p the flat form is an equivalent formula
 * \forall x0: ... \forall xn: \forall y0: ... \forall yn: u -> v where u are the matching constraints, a conjunction
 * of equalities, and v is a quantifier-free formula whose non-ground atoms are equalities between variables from
 * {x0, ... , xn, y0, ... , yn} called the flattened body.
 * <p>
 * The flat form is computed by starting with u = {true} and v = p. All terms t in u -> v are then repeatedly replaced
 * by a fresh variable x_t and the equation x_t = t is added to u until all non-ground terms have the form x or
 * f(x1, ... ,xn).
 *
 * @author Andre Challier <andre.challier@stud.tu-darmstadt.de>
 *
 */
public class FlattenedQuantifiedFormula {

    /** A set of equalities that build the matching constraints for this flattened quantified formula in conjunction */
    private ImmutableSet<Term> matchingConstraints;

    /** A quantifier-free formula consisting of ground terms and equalities between variables from x,y */
    private Term flattenedBody;

    /** The original quantified formula */ //TODO check if it's necessary to save this in here
    private Term qf;


    public FlattenedQuantifiedFormula(Term quantifiedFormula, TermServices services) {
        this.qf = quantifiedFormula;
        matchingConstraints = DefaultImmutableSet.<Term>nil();
        //matchingConstraints = matchingConstraints.add()
        assert (quantifiedFormula.op() instanceof Quantifier) : "Can not create a flattened quantified formula of an unquantified formula";

    }
}
