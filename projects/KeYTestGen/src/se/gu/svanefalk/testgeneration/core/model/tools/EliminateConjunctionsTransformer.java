package se.gu.svanefalk.testgeneration.core.model.tools;

import se.gu.svanefalk.testgeneration.util.transformers.AbstractTermTransformer;
import se.gu.svanefalk.testgeneration.util.transformers.NegationNormalFormTransformer;
import se.gu.svanefalk.testgeneration.util.transformers.TermTransformerException;
import de.uka.ilkd.key.logic.Term;

public class EliminateConjunctionsTransformer extends AbstractTermTransformer {

    private static EliminateConjunctionsTransformer instance = null;

    public static EliminateConjunctionsTransformer getInstance() {
        if (EliminateConjunctionsTransformer.instance == null) {
            EliminateConjunctionsTransformer.instance = new EliminateConjunctionsTransformer();
        }
        return EliminateConjunctionsTransformer.instance;
    }

    private EliminateConjunctionsTransformer() {
    }

    @Override
    public Term transform(final Term term) throws TermTransformerException {

        return transformTerm(term);
    }

    @Override
    protected Term transformOr(final Term term) throws TermTransformerException {

        final Term firstChild = term.sub(0);
        final Term secondChild = term.sub(1);

        final String firstChildName = firstChild.toString();
        final String secondChildName = secondChild.toString();

        if (firstChildName.length() < secondChildName.length()) {
            return transformTerm(firstChild);
        } else {
            return transformTerm(secondChild);
        }
    }
}