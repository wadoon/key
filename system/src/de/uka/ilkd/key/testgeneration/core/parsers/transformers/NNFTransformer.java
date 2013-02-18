package de.uka.ilkd.key.testgeneration.core.parsers.transformers;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;

/**
 * This transformer brings a Term into Negation Normal Form.
 * <p>
 * A Term is in NNF iff. the only negations it contains are negations of logical
 * atoms.
 * 
 * The algorithm used in this particular implementation was taken from:
 * <p>
 * (Huth and Ryan, <i>Logic in Computer Science</i>, 2nd Ed. Cambridge
 * University press, 2008)
 * 
 * @author christopher
 */
public class NNFTransformer extends AbstractTermTransformer {

    /**
     * Puts a Term into NNF.
     */
    @Override
    public Term transform(Term term) throws TermTransformerException {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    protected Term transformNot(Term term) throws TermTransformerException {

        if (hasChildren(term)) {
            Term child = term.sub(0);

            /*
             * If the child of this node is another NOT-node, then replace this
             * node with the child of that node, and proceed with parsing that
             * node as usual.
             */
            if (isNot(child)) {
                if (hasChildren(child)) {
                    return transformTerm(child.sub(0));
                }
            }

            /*
             * If the child of this node is an AND statement, apply De Morgans
             * laws in order to remove the negation.
             */
            else if (isAnd(child)) {

                /*
                 * Negate the two subterms to the AND operator.
                 */
                Term negatedFirstSub = termFactory.createTerm(Junctor.NOT,
                        child.sub(0));

                Term negatedSecondSub = termFactory.createTerm(Junctor.NOT,
                        child.sub(1));

                /*
                 * Parse them both normally.
                 */
                Term parsedFirstSub = transformTerm(negatedFirstSub);
                Term parsedSecondSub = transformTerm(negatedSecondSub);

                /*
                 * Finally, return an OR operator with the new terms as
                 * subterms.
                 */
                return termFactory.createTerm(Junctor.OR, parsedFirstSub,
                        parsedSecondSub);
            }

            /*
             * If the child of this node is an OR statement, we process it using
             * De Morgans laws, just as in the case with AND.
             */
            else if (isAnd(child)) {

                /*
                 * Negate the two subterms.
                 */
                Term negatedFirstSub = termFactory.createTerm(Junctor.NOT,
                        child.sub(0));

                Term negatedSecondSub = termFactory.createTerm(Junctor.NOT,
                        child.sub(1));

                /*
                 * Parse both negated subterms.
                 */
                Term parsedFirstSub = transformTerm(negatedFirstSub);
                Term parsedSecondSub = transformTerm(negatedSecondSub);

                /*
                 * Return the new AND operator.
                 */
                return termFactory.createTerm(Junctor.AND, parsedFirstSub,
                        parsedSecondSub);
            }
        }

        /*
         * The default case occurs if the child is something else than the cases
         * above, in which case we just move on.
         */
        return super.transformNot(term);
    }
}