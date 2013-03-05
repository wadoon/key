package de.uka.ilkd.key.testgeneration.core.oracle.generator;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.AbstractTermTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.ConjunctionNormalFormTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.OrderOperandsTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.RemoveSDPsTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.SimplifyConjunctionTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.SimplifyDisjunctionTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.TermTransformerException;

class TermToOracleTransformer extends AbstractTermTransformer {

    private final String separator;

    public TermToOracleTransformer(final String separator) {
        this.separator = separator;
    }

    /**
     * Simplifies a postcondition by removing {@link SortDependingFunction}
     * instances, {@link ObserverFunction} instances, as well as exception and
     * heap models. These are not needed (for now) for the purpose of expressing
     * correctness, and removing them makes the Term much more easy to work
     * with.
     * 
     * @param oracleTerm
     *            the Term
     * @return the simplified Term
     * @throws TermTransformerException
     *             in the event of a parse error (including structural errors in
     *             the Term itself.
     */
    @Override
    public Term transform(final Term term) throws TermTransformerException {

        Term oracleTerm = term;

        /*
         * Remove all SortDependingFunction instances from the Term.
         */
        oracleTerm = new RemoveSDPsTransformer(this.separator)
                .transform(oracleTerm);

        /*
         * Order the operands of the term
         */
        oracleTerm = new OrderOperandsTransformer().transform(oracleTerm);

        /*
         * Do the transformation
         */
        oracleTerm = this.transformTerm(oracleTerm);

        /*
         * Put it into Conjunctive Normal Form
         */
        oracleTerm = new ConjunctionNormalFormTransformer()
                .transform(oracleTerm);

        /*
         * Simplify the disjunctions in the postcondition
         */
        oracleTerm = new SimplifyDisjunctionTransformer().transform(oracleTerm);

        /*
         * Simplify the remaining conjunctions
         */
        oracleTerm = new SimplifyConjunctionTransformer().transform(oracleTerm);

        return oracleTerm;
    }

    /**
     * Simplifies an AND junctor by examining the operands. If one of them can
     * be simplified to null, the entire junction can be replaced by the second
     * operand. If both are simplified to null, the entire conjunction can be
     * removed (hence this method will return null as well).
     * 
     * @param term
     * @throws ModelGeneratorException
     */
    @Override
    protected Term transformAnd(final Term term)
            throws TermTransformerException {

        final Term firstChild = this.transformTerm(term.sub(0));
        final Term secondChild = this.transformTerm(term.sub(1));

        if ((firstChild != null) && (secondChild == null)) {
            return firstChild;
        }

        if ((firstChild == null) && (secondChild != null)) {
            return secondChild;
        }

        if ((firstChild != null) && (secondChild != null)) {
            return this.termFactory.createTerm(Junctor.AND, firstChild,
                    secondChild);
        }

        return null;
    }

    /**
     * In terms of logical representation, equality differs from the other
     * comparators (leq, geq etc) in the sense that it can be applied to boolean
     * values as well as numeric ones. Thus, it is treated differently in the
     * sense that we simplify it the same way that we simplify junctors.
     * 
     * @param term
     * @return
     * @throws ModelGeneratorException
     */
    @Override
    protected Term transformEquals(final Term term)
            throws TermTransformerException {

        /*
         * Handle the special case where the child is the exception type.
         */
        if (!this.isExceptionSort(term.sub(0))) {

            final Term firstChild = this.transformTerm(term.sub(0));
            final Term secondChild = this.transformTerm(term.sub(1));

            if ((firstChild != null) && (secondChild == null)) {
                return firstChild;
            }

            if ((firstChild == null) && (secondChild != null)) {
                return secondChild;
            }

            if ((firstChild != null) && (secondChild != null)) {
                return this.termFactory.createTerm(term.op(), firstChild,
                        secondChild);
            }
        }

        return null;
    }

    /**
     * Simplify a negation. If the child is simplified to null, simply return
     * null. Otherwise, create a new negation of the simplification of the
     * child.
     * 
     * @param term
     *            the term (logical negator) to simplify
     * @return the simplified negation
     * @throws TermTransformerException
     * @throws ModelGeneratorException
     */
    @Override
    protected Term transformNot(final Term term)
            throws TermTransformerException {

        final Term newChild = this.transformTerm(term.sub(0));

        if (newChild == null) {
            return null;
        }

        return this.termFactory.createTerm(Junctor.NOT, newChild);
    }

    /**
     * Simply remove {@link ObserverFunction} instances.
     */
    @Override
    protected Term transformObserverFunction(final Term term) {

        return null;
    }

    /**
     * Simplifies an OR junctor by examining the operands. If one of them can be
     * simplified to null, the entire junction can be replaced by the second
     * operand. If both are simplified to null, the entire conjunction can be
     * removed (hence this method will return null as well).
     * 
     * @param term
     * @throws ModelGeneratorException
     */
    @Override
    protected Term transformOr(final Term term) throws TermTransformerException {

        final Term firstChild = this.transformTerm(term.sub(0));
        final Term secondChild = this.transformTerm(term.sub(1));

        if ((firstChild != null) && (secondChild == null)) {
            return firstChild;
        }

        if ((firstChild == null) && (secondChild != null)) {
            return secondChild;
        }

        if ((firstChild != null) && (secondChild != null)) {
            return this.termFactory.createTerm(Junctor.OR, firstChild,
                    secondChild);
        }

        return null;
    }
}
