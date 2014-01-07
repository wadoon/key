package com.csvanefalk.keytestgen.core.oracle;

import com.csvanefalk.keytestgen.core.model.ModelGeneratorException;
import com.csvanefalk.keytestgen.util.transformers.*;
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
     * @param term the Term
     * @return the simplified Term
     * @throws TermTransformerException in the event of a parse error (including structural errors in
     *                                  the Term itself.
     */
    @Override
    public Term transform(final Term term) throws TermTransformerException {

        Term oracleTerm = term;

        /*
         * Remove all SortDependingFunction instances from the Term.
         */
        oracleTerm = RemoveSDPsTransformer.getInstance().transform(oracleTerm);

        /*
         * Remove all implications
         */
        oracleTerm = RemoveImplicationsTransformer.getInstance().transform(oracleTerm);

        /*
         * Remove all observerFunctions.
         */
        oracleTerm = RemoveObserverFunctionsTransformer.getInstance().transform(oracleTerm);

        /*
         * Order the operands of the term
         */
        oracleTerm = OrderOperandsTransformer.getInstance().transform(oracleTerm);

        /*
         * Do the transformation
         */
        oracleTerm = transformTerm(oracleTerm);

        /*
         * Put it into Conjunctive Normal Form
         */
        oracleTerm = ConjunctionNormalFormTransformer.getInstance().transform(oracleTerm);

        /*
         * Simplify the disjunctions in the postcondition
         */
        oracleTerm = SimplifyDisjunctionTransformer.getInstance().transform(oracleTerm);

        /*
         * Simplify the remaining conjunctions
         */
        oracleTerm = SimplifyConjunctionTransformer.getInstance().transform(oracleTerm);

        return oracleTerm;
    }

    /**
     * Simplifies an AND junctor by examining the operands. If one of them can
     * be simplified to null, the entire junction can be replaced by the second
     * operand. If both are simplified to null, the entire conjunction can be
     * removed (hence this method will return null as well).
     *
     * @param term the term
     * @throws ModelGeneratorException
     */
    @Override
    protected Term transformAnd(final Term term) throws TermTransformerException {

        final Term firstChild = transformTerm(term.sub(0));
        final Term secondChild = transformTerm(term.sub(1));

        if ((firstChild != null) && (secondChild == null)) {
            return firstChild;
        }

        if ((firstChild == null) && (secondChild != null)) {
            return secondChild;
        }

        if ((firstChild != null) && (secondChild != null)) {
            return termFactory.createTerm(Junctor.AND, firstChild, secondChild);
        }

        return null;
    }

    /**
     * Simplifies an EQUALS statement by examining the operands. If the first
     * operand is simplified to null, the entire statement can be removed since
     * it is now semanticallt useless.
     *
     * @param term the term the term
     * @throws ModelGeneratorException
     */
    @Override
    protected Term transformEquals(final Term term) throws TermTransformerException {

        final Term firstChild = transformTerm(term.sub(0));
        final Term secondChild = transformTerm(term.sub(1));

        if (firstChild == null) {
            return null;
        } else {

            return termFactory.createTerm(term.op(), firstChild, secondChild);
        }
    }

    /**
     * Remove formulas not needed to construct the oracle abstraction. These
     * include the various logical functions introduced by Key.
     */
    @Override
    protected Term transformFormula(final Term term) throws TermTransformerException {

        final String formulaName = term.op().name().toString();

        /*
         * Remove the common logical functions introduced by KeY, as they have
         * no meaning (?) with regard to the postcondition itself.
         */
        if (formulaName.equals("inInt") || formulaName.equals("java.lang.Object::<inv>")) {
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
    protected Term transformLocationVariable(final Term term) {

        /*
         * Remove the exception check introduced by KeY
         */
        final String variableName = term.op().name().toString();
        if (variableName.equals("exc")) {
            return null;
        } else {
            return term;
        }
    }

    /**
     * Simplify a negation. If the child is simplified to null, simply return
     * null. Otherwise, create a new negation of the simplification of the
     * child.
     *
     * @param term the term (logical negator) to simplify
     * @return the simplified negation
     * @throws TermTransformerException
     * @throws ModelGeneratorException
     */
    @Override
    protected Term transformNot(final Term term) throws TermTransformerException {

        final Term newChild = transformTerm(term.sub(0));

        if (newChild == null) {
            return null;
        }

        return termFactory.createTerm(Junctor.NOT, newChild);
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

        final Term firstChild = transformTerm(term.sub(0));
        final Term secondChild = transformTerm(term.sub(1));

        if ((firstChild != null) && (secondChild == null)) {
            return firstChild;
        }

        if ((firstChild == null) && (secondChild != null)) {
            return secondChild;
        }

        if ((firstChild != null) && (secondChild != null)) {
            return termFactory.createTerm(Junctor.OR, firstChild, secondChild);
        }

        return null;
    }
}