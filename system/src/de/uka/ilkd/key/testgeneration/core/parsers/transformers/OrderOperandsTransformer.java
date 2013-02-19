package de.uka.ilkd.key.testgeneration.core.parsers.transformers;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;

/**
 * Transformer which rebuilds a Term in such a way that all Junctors having the
 * same operands, also have them in the same order.
 * 
 * @author christopher
 * 
 */
public class OrderOperandsTransformer extends AbstractTermTransformer {

    @Override
    public Term transform(Term term) throws TermTransformerException {

        return transformTerm(term);
    }

    @Override
    protected Term transformAnd(Term term) throws TermTransformerException {

        Term transformedFirstChild = transformTerm(term.sub(0));
        Term transformedSecondChild = transformTerm(term.sub(1));

        String firstChildName = transformedFirstChild.toString();
        String secondChildName = transformedSecondChild.toString();

        int comparison = firstChildName.compareTo(secondChildName);
        if (comparison > 0) {
            return termFactory.createTerm(Junctor.AND, transformedSecondChild,
                    transformedFirstChild);
        } else {
            return termFactory.createTerm(Junctor.AND, transformedFirstChild,
                    transformedSecondChild);
        }
    }

    @Override
    protected Term transformOr(Term term) throws TermTransformerException {

        Term transformedFirstChild = transformTerm(term.sub(0));
        Term transformedSecondChild = transformTerm(term.sub(1));

        String firstChildName = transformedFirstChild.toString();
        String secondChildName = transformedSecondChild.toString();

        int comparison = firstChildName.compareTo(secondChildName);
        if (comparison > 0) {
            return termFactory.createTerm(Junctor.OR, transformedSecondChild,
                    transformedFirstChild);
        } else {
            return termFactory.createTerm(Junctor.OR, transformedFirstChild,
                    transformedSecondChild);
        }
    }

    @Override
    protected Term transformEquals(Term term) throws TermTransformerException {

        Term transformedFirstChild = transformTerm(term.sub(0));
        Term transformedSecondChild = transformTerm(term.sub(1));

        String firstChildName = transformedFirstChild.toString();
        String secondChildName = transformedSecondChild.toString();

        int comparison = firstChildName.compareTo(secondChildName);
        if (comparison > 0) {
            return termFactory.createTerm(term.op(), transformedSecondChild,
                    transformedFirstChild);
        } else {
            return termFactory.createTerm(term.op(), transformedFirstChild,
                    transformedSecondChild);
        }
    }
}
