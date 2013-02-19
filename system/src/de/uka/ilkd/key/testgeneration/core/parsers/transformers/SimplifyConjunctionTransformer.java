package de.uka.ilkd.key.testgeneration.core.parsers.transformers;

import java.util.HashSet;
import java.util.PriorityQueue;
import java.util.Set;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;

public class SimplifyConjunctionTransformer extends AbstractTermTransformer {

    /**
     * Simplifies all the disjunctions present in the term.
     * <p>
     * For example, given the following Term (human-readable):
     * 
     * <pre>
     * (a | b) &amp; c &amp; x &amp; c &amp; (a | b)
     * </pre>
     * 
     * this Transformer will produce the following:
     * 
     * <pre>
     * x &amp; c &amp; (a | b)
     * </pre>
     * 
     * @param term
     *            the term
     */
    @Override
    public Term transform(Term term) throws TermTransformerException {

        Term orderedTerm = new OrderOperandsTransformer().transform(term);
        return transformTerm(orderedTerm);
    }

    @Override
    protected Term transformAnd(Term term) throws TermTransformerException {

        Term firstChild = term.sub(0);
        Term secondChild = term.sub(1);

        /*
         * Collect all literals in the right subtree
         */
        Set<String> literals = new HashSet<String>();
        collectLiterals(secondChild, literals);

        /*
         * Simplify the left subtree
         */
        Term simplifiedFirstChild = simplify(firstChild, literals);

        /*
         * Depending on the outcome of the previous simplification, recursively
         * transform both subtrees, or just the right one.
         */
        if (simplifiedFirstChild == null) {
            return transform(secondChild);
        } else {
            Term transformedSimplifiedFirstChild = transformTerm(simplifiedFirstChild);
            Term transformedRightChild = transformTerm(secondChild);
            return termFactory.createTerm(Junctor.AND,
                    transformedSimplifiedFirstChild, transformedRightChild);
        }
    }

    /**
     * Simplifies a Term subtree depending on what literals are present in its
     * sibling (record in the literals set).
     * <p>
     * This method recursively transforms the subtree, removing all literals
     * which already occur in the trees sibling.
     * 
     * @param term
     * @param literals
     * @return
     */
    private Term simplify(Term term, Set<String> literals) {

        /*
         * If the term represents an OR statement, we simplify each child, and
         * return based on the outcome of this.
         */
        if (isAnd(term)) {

            Term firstChild = simplify(term.sub(0), literals);
            Term secondChild = simplify(term.sub(1), literals);

            if (firstChild != null && secondChild == null) {
                return firstChild;
            }

            if (firstChild == null && secondChild != null) {
                return secondChild;
            }

            if (firstChild != null && secondChild != null) {
                return termFactory.createTerm(Junctor.AND, firstChild,
                        secondChild);
            }

            return null;
        }

        /*
         * In any other case, we count the term as a literal. If this literal
         * has already been found in the Term, we remove it.
         */
        else {

            String termName = term.toString().trim();
            return literals.contains(termName) ? null : term;
        }
    }

    private void collectLiterals(Term term, Set<String> literals) {

        if (isAnd(term)) {

            collectLiterals(term.sub(0), literals);
            collectLiterals(term.sub(1), literals);
        } else {

            String termName = term.toString().trim();
            literals.add(termName);
        }
    }
}