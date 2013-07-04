package se.gu.svanefalk.testgeneration.util.transformers;

import se.gu.svanefalk.testgeneration.core.model.ModelGeneratorException;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;

public class RemoveObserverFunctionsTransformer extends AbstractTermTransformer {

    private static RemoveObserverFunctionsTransformer instance = null;

    public static RemoveObserverFunctionsTransformer getInstance() {
        if (RemoveObserverFunctionsTransformer.instance == null) {
            RemoveObserverFunctionsTransformer.instance = new RemoveObserverFunctionsTransformer();
        }
        return RemoveObserverFunctionsTransformer.instance;
    }

    private RemoveObserverFunctionsTransformer() {
    }

    @Override
    public Term transform(final Term term) throws TermTransformerException {
        return transformTerm(term);
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

        final Term firstChild = transformTerm(term.sub(0));
        final Term secondChild = transformTerm(term.sub(1));

        if ((firstChild != null) && (secondChild == null)) {
            if (firstChild.toString().equalsIgnoreCase("result")) {
                return term;
            } else {
                return firstChild;
            }
        }

        if ((firstChild == null) && (secondChild != null)) {
            if (firstChild.toString().equalsIgnoreCase("result")) {
                return term;
            } else {
                return secondChild;
            }
        }

        if ((firstChild != null) && (secondChild != null)) {
            return termFactory.createTerm(term.op(), firstChild, secondChild);
        }

        if ((firstChild == null) && (secondChild == null)) {

            return null;
        }

        return term;
    }

    @Override
    protected Term transformLocationVariable(final Term term) {

        if (TermParserTools.isExceptionSort(term)) {
            return null;
        }

        return super.transformLocationVariable(term);
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

        final Term newChild = transformTerm(term.sub(0));

        if (newChild == null) {
            return null;
        }

        return termFactory.createTerm(Junctor.NOT, newChild);
    }

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
