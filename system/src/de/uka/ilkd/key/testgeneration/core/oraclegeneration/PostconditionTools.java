package de.uka.ilkd.key.testgeneration.core.oraclegeneration;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.AbstractTermTransformer;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.RemoveSDPsTransformer;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.TermTransformerException;

/**
 * Contains various methods related to processing the postconditions of methods
 * in Java files.
 * 
 * @author christopher
 */
public class PostconditionTools {

    public static Term simplifyPostCondition(Term term, String separator)
            throws TermTransformerException {

        return new SimplifyPostConditionTransformer().simplifyPostCondition(
                term, separator);
    }

    private static class SimplifyPostConditionTransformer extends
            AbstractTermTransformer {

        /**
         * Simplifies a postcondition by removing {@link SortDependingFunction}
         * instances, {@link ObserverFunction} instances, as well as exception
         * and heap models. These are not needed (for now) for the purpose of
         * expressing correctness, and removing them makes the Term much more
         * easy to work with.
         * 
         * @param term
         *            the Term
         * @return the simplified Term
         * @throws TermTransformerException
         *             in the event of a parse error (including structural
         *             errors in the Term itself.
         */
        public Term simplifyPostCondition(Term term, String separator)
                throws TermTransformerException {

            /*
             * Remove all SortDependingFunction instances from the Term.
             */
            Term termWithoutSDFs = new RemoveSDPsTransformer(separator)
                    .removeSortDependingFunctions(term);

            return transformTerm(term);
        }

        /**
         * Simplify a negation. If the child is simplified to null, simply
         * return null. Otherwise, create a new negation of the simplification
         * of the child.
         * 
         * @param term
         *            the term (logical negator) to simplify
         * @return the simplified negation
         * @throws TermTransformerException
         * @throws ModelGeneratorException
         */
        @Override
        protected Term transformNot(Term term) throws TermTransformerException {

            Term newChild = transformTerm(term.sub(0));

            if (newChild == null) {
                return null;
            }

            return termFactory.createTerm(Junctor.NOT, newChild);
        }

        /**
         * Simplifies an AND junctor by examining the operands. If one of them
         * can be simplified to null, the entire junction can be replaced by the
         * second operand. If both are simplified to null, the entire
         * conjunction can be removed (hence this method will return null as
         * well).
         * 
         * @param term
         * @throws ModelGeneratorException
         */
        @Override
        protected Term transformAnd(Term term) throws TermTransformerException {

            Term firstChild = transformTerm(term.sub(0));
            Term secondChild = transformTerm(term.sub(1));

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

        /**
         * Simplifies an OR junctor by examining the operands. If one of them
         * can be simplified to null, the entire junction can be replaced by the
         * second operand. If both are simplified to null, the entire
         * conjunction can be removed (hence this method will return null as
         * well).
         * 
         * @param term
         * @throws ModelGeneratorException
         */
        @Override
        protected Term transformOr(Term term) throws TermTransformerException {

            Term firstChild = transformTerm(term.sub(0));
            Term secondChild = transformTerm(term.sub(1));

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

        /**
         * In terms of logical representation, equality differs from the other
         * comparators (leq, geq etc) in the sense that it can be applied to
         * boolean values as well as numeric ones. Thus, it is treated
         * differently in the sense that we simplify it the same way that we
         * simplify junctors.
         * 
         * @param term
         * @return
         * @throws ModelGeneratorException
         */
        @Override
        protected Term transformEquals(Term term)
                throws TermTransformerException {

            Term firstChild = transformTerm(term.sub(0));
            Term secondChild = transformTerm(term.sub(1));

            if (firstChild != null && secondChild == null) {
                return firstChild;
            }

            if (firstChild == null && secondChild != null) {
                return secondChild;
            }

            if (firstChild != null && secondChild != null) {
                return termFactory.createTerm(term.op(), firstChild,
                        secondChild);
            }

            return null;
        }

        /**
         * Simply remove {@link ObserverFunction} instances.
         */
        @Override
        protected Term transformObserverFunction(Term term) {

            return null;
        }
    }
}
