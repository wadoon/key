package se.gu.svanefalk.testgeneration.core.oracle;

import se.gu.svanefalk.testgeneration.core.model.ModelGeneratorException;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import se.gu.svanefalk.testgeneration.util.parsers.transformers.AbstractTermTransformer;
import se.gu.svanefalk.testgeneration.util.parsers.transformers.ConjunctionNormalFormTransformer;
import se.gu.svanefalk.testgeneration.util.parsers.transformers.OrderOperandsTransformer;
import se.gu.svanefalk.testgeneration.util.parsers.transformers.RemoveSDPsTransformer;
import se.gu.svanefalk.testgeneration.util.parsers.transformers.SimplifyConjunctionTransformer;
import se.gu.svanefalk.testgeneration.util.parsers.transformers.SimplifyDisjunctionTransformer;
import se.gu.svanefalk.testgeneration.util.parsers.transformers.TermTransformerException;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.SortDependingFunction;

class SimplifyPostconditionTransformer extends AbstractTermTransformer {

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
        oracleTerm = new RemoveSDPsTransformer().transform(oracleTerm);

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
     *            the term
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
     * Simplifies an EQUALS statement by examining the operands. If the first
     * operand is simplified to null, the entire statement can be removed since
     * it is now semanticallt useless.
     * 
     * @param term
     *            the term the term
     * @throws ModelGeneratorException
     */
    @Override
    protected Term transformEquals(final Term term)
            throws TermTransformerException {

        final Term firstChild = this.transformTerm(term.sub(0));
        final Term secondChild = this.transformTerm(term.sub(1));

        if (firstChild == null) {
            return null;
        } else {

            return this.termFactory.createTerm(term.op(), firstChild,
                    secondChild);
        }
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

    /**
     * Remove formulas not needed to construct the oracle abstraction. These
     * include the various logical functions introduced by Key.
     */
    @Override
    protected Term transformFormula(Term term) throws TermTransformerException {

        String formulaName = term.op().name().toString();

        /*
         * Remove the common logical functions introduced by KeY, as they have
         * no meaning (?) with regard to the postcondition itself.
         */
        if (formulaName.equals("inInt")
                || formulaName.equals("java.lang.Object::<inv>")) {
            return null;
        } else {
            return term;
        }
    }

    /**
     * Remove variables not needed to construct the oracle abstraction, in
     * particular the ones representing exceptions.
     */
    @Override
    protected Term transformLocationVariable(Term term) {

        /*
         * Remove the exception check introduced by KeY
         */
        String variableName = term.op().name().toString();
        if (variableName.equals("exc")) {
            return null;
        } else {
            return term;
        }
    }
}