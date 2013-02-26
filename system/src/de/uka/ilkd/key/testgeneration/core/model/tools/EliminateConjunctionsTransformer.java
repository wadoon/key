package de.uka.ilkd.key.testgeneration.core.model.tools;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.AbstractTermTransformer;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.TermTransformerException;

public class EliminateConjunctionsTransformer extends AbstractTermTransformer {

    @Override
    public Term transform(Term term) throws TermTransformerException {

        return transformTerm(term);
    }

    @Override
    protected Term transformOr(Term term) throws TermTransformerException {

        Term firstChild = term.sub(0);
        Term secondChild = term.sub(1);

        String firstChildName = firstChild.toString();
        String secondChildName = secondChild.toString();

        if (firstChildName.length() < secondChildName.length()) {
            return transformTerm(firstChild);
        } else {
            return transformTerm(secondChild);
        }
    }
}