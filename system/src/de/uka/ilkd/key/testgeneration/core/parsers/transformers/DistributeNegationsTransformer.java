package de.uka.ilkd.key.testgeneration.core.parsers.transformers;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * This transformer will simplify all instances of negations of junctions
 * according to De Morgans laws.
 */
public class DistributeNegationsTransformer extends AbstractTermTransformer {

    @Override
    public Term transform(Term term) throws TermTransformerException {

        return transformTerm(term);

    }

    @Override
    protected Term transformNot(Term term) throws TermTransformerException {

        Term child = term.sub(0);

        if (isAnd(child) || isOr(child)) {
            Term newChild;
            if (isAnd(child)) {
                newChild = distributeNegation(child, Junctor.OR);
            } else {
                newChild = distributeNegation(child, Junctor.AND);
            }
            return transformTerm(newChild);

        } else {
            return super.transformNot(term);
        }
    }

    private Term distributeNegation(Term term, Operator targetOperator) {

        /*
         * Extract the children and distribute the negation over them.
         */
        Term firstChild = term.sub(0);
        Term secondChild = term.sub(1);

        Term newFirstChild = negateTerm(firstChild);
        Term newSecondChild = negateTerm(secondChild);

        /*
         * Construct and return the new junction
         */
        return termFactory.createTerm(targetOperator, newFirstChild,
                newSecondChild);
    }

    /**
     * Negates a term. If the term is already negated, remove the existing
     * negation. If it is not negated, then negate it.
     * 
     * @param term
     * @return
     */
    private Term negateTerm(Term term) {
        if (isNot(term.sub(0))) {
            return term;
        } else {
            return termFactory.createTerm(Junctor.NOT, term);
        }
    }
}
