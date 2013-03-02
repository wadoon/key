package de.uka.ilkd.key.testgeneration.core.model.tools;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.AbstractTermTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.TermTransformerException;

public class EliminateConjunctionsTransformer extends AbstractTermTransformer {

    @Override
    public Term transform(final Term term) throws TermTransformerException {

        return this.transformTerm(term);
    }

    @Override
    protected Term transformOr(final Term term) throws TermTransformerException {

        final Term firstChild = term.sub(0);
        final Term secondChild = term.sub(1);

        final String firstChildName = firstChild.toString();
        final String secondChildName = secondChild.toString();

        if (firstChildName.length() < secondChildName.length()) {
            return this.transformTerm(firstChild);
        } else {
            return this.transformTerm(secondChild);
        }
    }
}