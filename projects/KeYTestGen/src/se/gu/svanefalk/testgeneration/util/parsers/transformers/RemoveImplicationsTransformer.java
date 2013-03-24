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

    /**
     * Transforms a {@link Term} by replacing all implications a -> b with the
     * equivalent form !a \/ b.
     * 
     * @author christopher
     */
    @Override
    public Term transform(Term term) throws TermTransformerException {

        return transformTerm(term);
    }

    @Override
    protected Term transformImplication(Term term)
            throws TermTransformerException {

        final Term newFirstChild = this.transformTerm(term.sub(0));
        final Term negatedNewFirstChild = this.termFactory.createTerm(
                Junctor.NOT, newFirstChild);

        final Term newSecondChild = this.transformTerm(term.sub(1));

        return this.termFactory.createTerm(Junctor.OR, negatedNewFirstChild,
                newSecondChild);
    }
}