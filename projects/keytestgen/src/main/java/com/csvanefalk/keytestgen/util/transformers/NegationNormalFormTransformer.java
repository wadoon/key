package com.csvanefalk.keytestgen.util.transformers;

import com.csvanefalk.keytestgen.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;

/**
 * This transformer brings a Term into Negation Normal Form.
 * <p/>
 * A Term is in NNF iff. the only negations it contains are negations of logical
 * atoms.
 *
 * @author christopher
 */
public class NegationNormalFormTransformer extends AbstractTermTransformer {

    private static NegationNormalFormTransformer instance = null;

    public static NegationNormalFormTransformer getInstance() {
        if (NegationNormalFormTransformer.instance == null) {
            NegationNormalFormTransformer.instance = new NegationNormalFormTransformer();
        }
        return NegationNormalFormTransformer.instance;
    }

    private NegationNormalFormTransformer() {
    }

    /**
     * Puts a Term into Negation Normal Form, using the following algorithm:
     * <p/>
     * <pre>
     * Pre: x is implication free and in Negation Normal Form
     * Post: NNF(x) computes and equivalent NNF for x
     * function NNF(x):
     * begin function
     *     case
     *         x is a literal : return x
     *         x is !!x1 : return NNF(x)
     *         x is x1 AND x2 : return NNF(x1) AND NNF(x2)
     *         x is x1 OR x2 : return NNF(x1) OR NNF(x2)
     *         x is !(x1 AND x2) : return NNF(!x1) OR NNF(!x2)
     *         x is !(x1 OR x2) : return NNF(!x1) AND NNF(!x2)
     *     end case
     * end function
     * </pre>
     * <p/>
     * The algorithm was taken from:
     * <p/>
     * (Huth and Ryan, <i>Logic in Computer Science</i>, page 62, 2nd Ed.
     * Cambridge University press, 2008)
     */
    @Override
    public Term transform(final Term term) throws TermTransformerException {
        return transformTerm(term);
    }

    @Override
    protected Term transformNot(final Term term)
            throws TermTransformerException {

        if (TermParserTools.hasChildren(term)) {
            final Term child = term.sub(0);

            /*
             * If the child of this node is another NOT-node, then replace this
             * node with the child of that node, and proceed with parsing that
             * node as usual.
             */
            if (TermParserTools.isNot(child)) {
                if (TermParserTools.hasChildren(child)) {
                    return transformTerm(child.sub(0));
                }
            }

            /*
             * If the child of this node is an AND statement, apply De Morgans
             * laws in order to remove the negation.
             */
            else if (TermParserTools.isAnd(child)) {

                /*
                 * Negate the two subterms to the AND operator.
                 */
                final Term negatedFirstSub = termFactory.createTerm(
                        Junctor.NOT, child.sub(0));

                final Term negatedSecondSub = termFactory.createTerm(
                        Junctor.NOT, child.sub(1));

                /*
                 * Parse them both normally.
                 */
                final Term parsedFirstSub = transformTerm(negatedFirstSub);
                final Term parsedSecondSub = transformTerm(negatedSecondSub);

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
            else if (TermParserTools.isAnd(child)) {

                /*
                 * Negate the two subterms.
                 */
                final Term negatedFirstSub = termFactory.createTerm(
                        Junctor.NOT, child.sub(0));

                final Term negatedSecondSub = termFactory.createTerm(
                        Junctor.NOT, child.sub(1));

                /*
                 * Parse both negated subterms.
                 */
                final Term parsedFirstSub = transformTerm(negatedFirstSub);
                final Term parsedSecondSub = transformTerm(negatedSecondSub);

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