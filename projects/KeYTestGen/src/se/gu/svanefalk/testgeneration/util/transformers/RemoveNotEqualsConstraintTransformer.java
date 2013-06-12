package se.gu.svanefalk.testgeneration.util.transformers;

import de.uka.ilkd.key.logic.Term;

public class RemoveNotEqualsConstraintTransformer extends
        AbstractTermTransformer {

    private static RemoveNotEqualsConstraintTransformer instance = null;

    public static RemoveNotEqualsConstraintTransformer getInstance() {
        if (RemoveNotEqualsConstraintTransformer.instance == null) {
            RemoveNotEqualsConstraintTransformer.instance = new RemoveNotEqualsConstraintTransformer();
        }
        return RemoveNotEqualsConstraintTransformer.instance;
    }

    private RemoveNotEqualsConstraintTransformer() {
    }

    @Override
    public Term transform(Term term) throws TermTransformerException {
        return transformTerm(term);
        term.
    }
}
