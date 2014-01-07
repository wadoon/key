package com.csvanefalk.keytestgen.core.model.tools;

import com.csvanefalk.keytestgen.StringConstants;
import com.csvanefalk.keytestgen.core.model.ModelGeneratorException;
import com.csvanefalk.keytestgen.util.parsers.TermParserTools;
import com.csvanefalk.keytestgen.util.transformers.AbstractTermTransformer;
import com.csvanefalk.keytestgen.util.transformers.TermTransformerException;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Provides various methods for processing the pathconditions for
 * {@link IExecutionNode} instances.
 *
 * @author christopher
 */
public class ModelGenerationTools {

    private static class TermSimplificationTransformer extends AbstractTermTransformer {

        /**
         * Given an initial {@link Term}, constructs a simpler Term which
         * "localizes" all occurences of primitive datatypes, by transforming
         * the instances of {@link SortDependingFunction} which contain them.
         * <p/>
         * As an example of how this works, consider the case where we have an
         * instace of some class <code>Base</code> named "base", which as a
         * field has an instance of some other class <code>Inner</code> named
         * "inner", which in turn has a local instance of an
         * <code>integer </code> named "localInt. Normally, simply transforming
         * such a construct to an SMT-LIB formula would result in a needlesly
         * complex expression and model, which is a waste of both resources and
         * time invested in developing additional parsers to understand it.
         * <p/>
         * What we do instead is to simply transform the construct into a local
         * variable of our base class, giving it a name corresponding to its
         * nesting order. In our case, such a name migh be
         * "base$nested$localInt". When all variables have been processed like
         * this, we end up with a greatly simplified term which can easily be
         * expressed as an SMT-LIB construct.
         * <p/>
         * This process will also remove all implied properties of internal
         * objects, such as not-null requirements, since these are not needed in
         * the simplified formula, and would only further pollute the SMT-LIB
         * expression. Further, it will simplify the formula by removing
         * unnecessary conjuntions.
         *
         * @param term the term to process
         * @return the simplified term
         * @throws ModelGeneratorException
         */
        @Override
        public Term transform(final Term term) throws TermTransformerException {

            return transformTerm(term);
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
        protected Term transformAnd(final Term term) throws TermTransformerException {

            final Term firstChild = transformTerm(term.sub(0));
            final Term secondChild = transformTerm(term.sub(1));

            if ((firstChild != null) && (secondChild == null)) {
                return firstChild;
            }

            if ((firstChild == null) && (secondChild != null)) {
                return secondChild;
            }

            if ((firstChild != null) && (secondChild != null)) {
                return termFactory.createTerm(Junctor.AND, firstChild, secondChild);
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
        protected Term transformEquals(final Term term) throws TermTransformerException {

            final Term firstChild = transformTerm(term.sub(0));
            final Term secondChild = transformTerm(term.sub(1));

            if ((firstChild != null) && (secondChild == null)) {

                /*
                 * Make a distinction based on whether the equality is between
                 * primitive or reference types.
                 */
                if (TermParserTools.isPrimitiveType(firstChild)) {
                    return firstChild;
                } else {
                    return null;
                }
            }

            if ((firstChild == null) && (secondChild != null)) {
                if (TermParserTools.isPrimitiveType(firstChild)) {
                    return secondChild;
                } else {
                    return null;
                }
            }

            if ((firstChild != null) && (secondChild != null)) {
                return termFactory.createTerm(term.op(), firstChild, secondChild);
            }

            return null;
        }

        /**
         * Simplify a negation. If the child is simplified to null, simply
         * return null. Otherwise, create a new negation of the simplification
         * of the child.
         *
         * @param term the term (logical negator) to simplify
         * @return the simplified negation
         * @throws TermTransformerException
         * @throws ModelGeneratorException
         */
        @Override
        protected Term transformNot(final Term term) throws TermTransformerException {

            final Term newChild = transformTerm(term.sub(0));

            if (newChild == null) {
                return null;
            }

            return termFactory.createTerm(Junctor.NOT, newChild);
        }

        /**
         * The transformation of the nulltype is simply to return a null value.
         */
        @Override
        protected Term transformNull(final Term term) {

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
        protected Term transformOr(final Term term) throws TermTransformerException {

            final Term firstChild = transformTerm(term.sub(0));
            final Term secondChild = transformTerm(term.sub(1));

            if ((firstChild != null) && (secondChild == null)) {
                return firstChild;
            }

            if ((firstChild == null) && (secondChild != null)) {
                return secondChild;
            }

            if ((firstChild != null) && (secondChild != null)) {
                return termFactory.createTerm(Junctor.OR, firstChild, secondChild);
            }

            return null;
        }

        /**
         * Given an {@link Term} of type {@link SortDependingFunction}, with a
         * primitive type as its sort, resolve the nesting hierarchy for this
         * variable, and encode this information as a new local variable, whose
         * name will depend on the classes involved in the nesting hierarchy.
         * For example, the int value x in the hiearchy
         * main.nested.other.yetanother.x will be renamed
         * "main$nested$other$yetanother$x", and treated simply as a local
         * variable in the object main.
         *
         * @param term the term to process
         * @return a Term representing the nested variable as a local variable
         */
        @Override
        protected Term transformSortDependentFunction(final Term term) {

            /*
             * Check if the base type of the selection statement is a primitive
             * type (we do not handle anything else). If so, create an alias for
             * the nested variable, and return everything else as a new
             * LocationVariable.
             */
            if (TermParserTools.isPrimitiveType(term)) {

                final ProgramElementName resolvedVariableName = new ProgramElementName(TermParserTools.resolveIdentifierString(
                        term,
                        ModelGenerationTools.SEPARATOR));

                final LocationVariable resolvedVariable = new LocationVariable(resolvedVariableName, term.sort());

                return termFactory.createTerm(resolvedVariable);
            }

            return null;
        }

        /**
         * Simplifying ordinary Terms only amounts to removing all Boolean typed
         * variables and constants in the Term.
         */
        @Override
        public Term transformTerm(final Term term) throws TermTransformerException {

            /*
             * Booleans are removed without reservation
             */
            if (TermParserTools.isBoolean(term) || TermParserTools.isIfThenElse(term)) {
                return null;
            }
            return super.transformTerm(term);
        }
    }

    private static final String SEPARATOR = StringConstants.FIELD_SEPARATOR.toString();

    private static final TermSimplificationTransformer termSimplificationTransformer = new TermSimplificationTransformer();

    /**
     * Given an initial {@link Term}, constructs a simpler Term which
     * "localizes" all occurences of primitive datatypes, by transforming the
     * instances of {@link SortDependingFunction} which contain them.
     * <p/>
     * As an example of how this works, consider the case where we have an
     * instace of some class <code>Base</code> named "base", which as a field
     * has an instance of some other class <code>Inner</code> named "inner",
     * which in turn has a local instance of an <code>integer </code> named
     * "localInt. Normally, simply transforming such a construct to an SMT-LIB
     * formula would result in a needlesly complex expression and model, which
     * is a waste of both resources and time invested in developing additional
     * parsers to understand it.
     * <p/>
     * What we do instead is to simply transform the construct into a local
     * variable of our base class, giving it a name corresponding to its nesting
     * order. In our case, such a name migh be "base$nested$localInt". When all
     * variables have been processed like this, we end up with a greatly
     * simplified term which can easily be expressed as an SMT-LIB construct.
     * <p/>
     * This process will also remove all implied properties of internal objects,
     * such as not-null requirements, since these are not needed in the
     * simplified formula, and would only further pollute the SMT-LIB
     * expression. Further, it will simplify the formula by removing unnecessary
     * conjuntions.
     *
     * @param term the term to process
     * @return the simplified term
     * @throws TermTransformerException
     * @throws ModelGeneratorException
     */
    public static Term simplifyTerm(final Term targetNodeCondition) throws TermTransformerException {

        return ModelGenerationTools.termSimplificationTransformer.transform(targetNodeCondition);
    }

    private ModelGenerationTools() {

    }
}