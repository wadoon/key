package se.gu.svanefalk.testgeneration.util.parsers.transformers;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;

/**
 * Instances of this transformer removes implications from terms.
 * 
 * @author christopher
 * 
 */
public class RemoveImplicationsTransformer extends AbstractTermTransformer {

    private static RemoveImplicationsTransformer instance = null;

    public static RemoveImplicationsTransformer getInstance() {
        if (RemoveImplicationsTransformer.instance == null) {
            RemoveImplicationsTransformer.instance = new RemoveImplicationsTransformer();
        }
        return RemoveImplicationsTransformer.instance;
    }

    private RemoveImplicationsTransformer() {
    }

    /**
     * Transforms a {@link Term} by replacing all implications a -> b with the
     * equivalent form !a \/ b.
     * 
     * @author christopher
     */
    @Override
    public Term transform(final Term term) throws TermTransformerException {

        return transformTerm(term);
    }

    @Override
    protected Term transformImplication(final Term term)
            throws TermTransformerException {

        final Term newFirstChild = transformTerm(term.sub(0));
        final Term negatedNewFirstChild = termFactory.createTerm(Junctor.NOT,
                newFirstChild);

        final Term newSecondChild = transformTerm(term.sub(1));

        return termFactory.createTerm(Junctor.OR, negatedNewFirstChild,
                newSecondChild);
    }
}