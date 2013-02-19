package de.uka.ilkd.key.testgeneration.core.parsers.transformers;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;

/**
 * This Transformer simplifies the disjunctions present in a Term.
 * 
 * @author christopher
 * 
 */
public class SimplifyDisjunctionTransformer extends AbstractTermTransformer {

    /**
     * Simplifies all the disjunctions present in the term.
     * <p>
     * For example, given the following Term (human-readable):
     * 
     * <pre>
     * (a &amp; b) | c | x | c | (a &amp; b)
     * </pre>
     * 
     * this Transformer will produce the following:
     * 
     * <pre>
     * x | c | (a &amp; b)
     * </pre>
     * 
     * @param term
     *            the term
     */
    @Override
    public Term transform(Term term) throws TermTransformerException {

        if (isOr(term)) {

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
             * Depending on the outcome of the previous simplification,
             * recursively transform both subtrees, or just the right one.
             */
            if (simplifiedFirstChild == null) {
                return transform(secondChild);
            } else {
                Term transformedSimplifiedFirstChild = transform(simplifiedFirstChild);
                Term transformedRightChild = transform(secondChild);
                return termFactory.createTerm(Junctor.OR,
                        transformedSimplifiedFirstChild, transformedRightChild);
            }
        }

        return term;
    }

    private void collectLiterals(Term term, Set<String> literals) {

        if (isOr(term)) {

            collectLiterals(term.sub(0), literals);
            collectLiterals(term.sub(1), literals);
        } else {

            String termName = term.toString().trim();
            literals.add(termName);
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
        if (isOr(term)) {

            Term firstChild = simplify(term.sub(0), literals);
            Term secondChild = simplify(term.sub(1), literals);

            if (firstChild != null && secondChild == null) {
                return firstChild;
            }

            if (firstChild == null && secondChild != null) {
                return secondChild;
            }

            if (firstChild != null && secondChild != null) {
                return termFactory.createTerm(Junctor.OR, firstChild,
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
            return literals.contains(termName) ? term : null;
        }
    }
}