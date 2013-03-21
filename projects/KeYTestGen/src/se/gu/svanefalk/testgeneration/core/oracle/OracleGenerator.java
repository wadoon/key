package se.gu.svanefalk.testgeneration.core.oracle;

import java.util.HashSet;
import java.util.Set;

import se.gu.svanefalk.testgeneration.StringConstants;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaMethod;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.Oracle;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleBooleanExpression;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleClause;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserException;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import se.gu.svanefalk.testgeneration.util.parsers.transformers.TermTransformerException;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfExThenElse;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

/**
 * API singleton for the oraclegeneration package.
 * <p>
 * Provides services for turning the postconditions of Java methods into oracle
 * {@link Term} instances.
 * 
 * @author christopher
 */
public enum OracleGenerator {
    INSTANCE;

    /**
     * Transformer used in order to transform {@link Term} instances
     * representing postconditions into a form suitable for turning them into
     * Oracles.
     */
    private final OracleTermTransformer oracleTermTransformer = new OracleTermTransformer(
            this.SEPARATOR);

    /**
     * Separator to use when resolving {@link SortDependingFunction} instances.
     */
    private final String SEPARATOR = StringConstants.FIELD_SEPARATOR.toString();

    private void constructClause(final Term term,
            final Set<OracleClause> clauses) throws OracleGeneratorException {

        /*
         * The clause to be constructed.
         */
        OracleClause clause = null;

        /*
         * Expressions belonging to the Clause.
         */
        final Set<OracleBooleanExpression> expressions = new HashSet<OracleBooleanExpression>();

        /*
         * Since the formula is in CNF, all occurences of AND junctions will be
         * in direct parent-child relationships with one another.
         * 
         * We hence start by checking if either of the children is an AND
         * junctor. If either is, we recursively continue to construct
         * Conjunctions for that child, while at the same time completing the
         * Conjunction for the current node by resolving the expression related
         * to it, which will in this case be present in the other child.
         * 
         * The base case is if neither of the children represent an AND-node. In
         * this case we simply resolve the expressions represented by both
         * children and return.
         */
        final Term firstChild = term.sub(0);
        final Term secondChild = term.sub(1);

        if (TermParserTools.isAnd(firstChild)) {
            this.constructClause(firstChild, clauses);
            this.constructExpressions(secondChild, expressions);

        } else if (TermParserTools.isAnd(secondChild)) {
            this.constructClause(secondChild, clauses);
            this.constructExpressions(firstChild, expressions);

        } else {
            this.constructExpressions(firstChild, expressions);
            this.constructExpressions(secondChild, expressions);
        }

        clause = new OracleClause(expressions);
        clauses.add(clause);
    }

    /**
     * Transforms a {@link Term} representing the AND junctor.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected OracleBooleanExpression constructExpressionFromAnd(final Term term)
            throws OracleGeneratorException {
        /*
         * final Term firstChild = this.transformTerm(term.sub(0)); final Term
         * secondChild = this.transformTerm(term.sub(1));
         */
        return null;
    }

    /**
     * Transforms a {@link Term} which represents a binary comparator. Such
     * functions include GreaterOrEquals, GreaterThan, LessOrEquals, and
     * LessThan. These are no explicitly defined as KeY operators, and are as
     * such recognized by their sorts.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromBinaryFunction(
            final Term term) throws OracleGeneratorException {
        /*
         * final Term newTerm = this.termFactory.createTerm(term.op(),
         * firstChild, secondChild);
         */
        return null;
    }

    private OracleBooleanExpression constructExpressionFromBooleanConstant(
            final Term term) {
        return null;
    }

    /**
     * Transforms a {@link Term} representing {@link Equality}.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromEquals(
            final Term term) throws OracleGeneratorException {
        /*
         * final Term firstChild =
         * this.constructExpressionFromTerm(term.sub(0)); final Term secondChild
         * = this.constructExpressionFromTerm(term.sub(1));
         * 
         * return this.termFactory.createTerm(term.op(), firstChild,
         * secondChild);
         */
        return null;
    }

    /**
     * Transforms a {@link Term} which represents some instance of a
     * {@link Function}.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromFunction(
            final Term term) throws OracleGeneratorException {

        try {

            /*
             * Order is crucial for proper resolution here, as the precise,
             * legitimate parent-child relationships between various
             * Function-type terms are not excplicitly spelled out in terms of
             * type relationships.
             */
            if (TermParserTools.isNullSort(term)) {
                return this.constructExpressionFromNull(term);
            }

            if (TermParserTools.isSortDependingFunction(term)) {
                return this.constructExpressionFromSortDependentFunction(term);
            }

            if (TermParserTools.isBinaryFunction(term)) {
                return this.constructExpressionFromBinaryFunction(term);
            }

            if (TermParserTools.isUnaryFunction(term)) {
                return this.constructExpressionFromUnaryFunction(term);
            }

            if (TermParserTools.isLiteral(term)) {
                return this.constructExpressionFromLiteral(term);
            }

            if (TermParserTools.isObserverFunction(term)) {
                return this.constructExpressionFromObserverFunction(term);

            }

            if (TermParserTools.isBooleanConstant(term)) {
                return this.constructExpressionFromBooleanConstant(term);
            }

        } catch (final TermParserException e) {

            throw new OracleGeneratorException(e.getMessage());
        }

        throw new OracleGeneratorException("Unsupported Function: "
                + term.op().name());
    }

    /**
     * Transforms a {@link Term} which represents an {@link IfExThenElse}
     * structure (i.e. its {@link Operator} is of this type).
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromIfExThenElse(
            final Term term) {

        return null;
    }

    /**
     * Transforms a {@link Term} which represents an {@link IfThenElse}
     * structure (i.e. its {@link Operator} is of this type).
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromIfThenElse(
            final Term term) {

        return null;
    }

    /**
     * Transforms a {@link Term} representing a Junctor, i.e. AND, OR, NOT.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     * @throws OracleGeneratorException
     */
    private OracleBooleanExpression constructExpressionFromJunctor(
            final Term term) throws OracleGeneratorException,
            OracleGeneratorException {

        if (TermParserTools.isAnd(term)) {
            return this.constructExpressionFromAnd(term);

        } else if (TermParserTools.isOr(term)) {
            return this.constructExpressionFromOr(term);

        } else if (TermParserTools.isEquals(term)) {
            return this.constructExpressionFromEquals(term);

        } else if (TermParserTools.isNot(term)) {
            return this.constructExpressionFromNot(term);
        }

        throw new OracleGeneratorException("Unsupported Junctor: "
                + term.op().name());
    }

    /**
     * Transforms a {@link Term} representing a Literal.
     * 
     * @param term
     * @return
     * @throws OracleGeneratorException
     */
    private OracleBooleanExpression constructExpressionFromLiteral(
            final Term term) throws OracleGeneratorException {

        /*
         * Literals may or may not declare children, such as 1(#);
         */
        if (!term.subs().isEmpty()) {
            // final Term child = this.constructExpressionFromTerm(term.sub(0));
            return null;
        } else {
            return null;
        }
    }

    /**
     * Transforms a {@link Term} which represents an {@link LocationVariable}
     * structure (i.e. its {@link Operator} is of this type).
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromLocationVariable(
            final Term term) {

        return null;
    }

    /**
     * Transforms a {@link Term} representing a the NOT junctor.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromNot(final Term term)
            throws OracleGeneratorException {

        // final Term newChild = this.constructExpressionFromTerm(term.sub(0));

        return null;
    }

    /**
     * Transforms a {@link Term} which represents a null element, i.e. it has
     * the sort {@link NullSort}.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromNull(final Term term) {

        return null;
    }

    /**
     * Transforms a {@link Term} representing an {@link ObserverFunction}.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromObserverFunction(
            final Term term) {

        if (TermParserTools.isProgramMethod(term)) {
            return this.constructExpressionFromProgramMethod(term);
        }

        return null;
    }

    /**
     * Transforms a {@link Term} representing an OR-junctor.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromOr(final Term term)
            throws OracleGeneratorException {
        /*
         * final Term firstChild =
         * this.constructExpressionFromTerm(term.sub(0)); final Term secondChild
         * = this.constructExpressionFromTerm(term.sub(1));
         */
        return null;
    }

    /**
     * Transforms a {@link Term} representing a {@link ProgramMethod}.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromProgramMethod(
            final Term term) {

        return null;
    }

    /**
     * Transforms a {@link Term} which represents a {@link ProgramVariable}
     * structure (i.e. its {@link Operator} is of this type).
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromProgramVariable(
            final Term term) throws OracleGeneratorException {

        if (TermParserTools.isLocationVariable(term)) {
            return this.constructExpressionFromLocationVariable(term);
        }

        throw new OracleGeneratorException("Unsupported SortedOperator: "
                + term.op().name());
    }

    /**
     * Transforms a {@link Term} which represents an
     * {@link SortDependingFunction} structure (i.e. its {@link Operator} is of
     * this type).
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromSortDependentFunction(
            final Term term) {

        return null;
    }

    /**
     * Transforms a {@link Term} which represents some kind of
     * {@link SortedOperator}.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromSortedOperator(
            final Term term) throws OracleGeneratorException {

        if (TermParserTools.isFunction(term)) {
            return this.constructExpressionFromFunction(term);
        }

        if (TermParserTools.isEquals(term)) {
            return this.constructExpressionFromEquals(term);
        }

        if (TermParserTools.isJunctor(term)) {
            return this.constructExpressionFromJunctor(term);
        }

        if (TermParserTools.isProgramVariable(term)) {
            return this.constructExpressionFromProgramVariable(term);
        }

        throw new OracleGeneratorException("Unsupported SortedOperator: "
                + term.op().name());
    }

    /**
     * The top level function for constructExpressionFroming a {@link Term}
     * instance. This function will do a preliminary check to see whether the
     * top-level operator of the Term is a basic {@link Operator} or a
     * {@link SortedOperator}, and proceed with parsing from there.
     * 
     * @param term
     * @return
     * @throws OracleGeneratorException
     */
    public OracleBooleanExpression constructExpressionFromTerm(final Term term)
            throws OracleGeneratorException {

        /*
         * Order matters here, since SortedOperator is a subclass of Operator.
         */
        if (TermParserTools.isSortedOperator(term)) {
            return this.constructExpressionFromSortedOperator(term);

        } else if (TermParserTools.isIfExThenElse(term)) {
            return this.constructExpressionFromIfExThenElse(term);

        } else if (TermParserTools.isIfThenElse(term)) {
            return this.constructExpressionFromIfThenElse(term);

        }

        throw new OracleGeneratorException(
                "Attempting to construct Oracle from corrupt Term. Expected SortedOperator or IfThenElse, but found "
                        + term.op().name());
    }

    /**
     * Transforms a {@link Term} representing a unary function, such as NOT.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleBooleanExpression constructExpressionFromUnaryFunction(
            final Term term) throws OracleGeneratorException {

        // final Term child = this.constructExpressionFromTerm(term.sub(0));

        return null;
    }

    private void constructExpressions(final Term term,
            final Set<OracleBooleanExpression> expressions)
            throws OracleGeneratorException {

        /*
         * If the Term is an Or-term, resolve both sub-expressions recursively
         */
        if (TermParserTools.isOr(term)) {
            this.constructExpressions(term.sub(0), expressions);
            this.constructExpressions(term.sub(1), expressions);
        } else {

            final OracleBooleanExpression expression = this
                    .constructExpressionFromTerm(term);
            expressions.add(expression);
        }
    }

    /**
     * Creates a Test Oracle for the provided method. The Oracle will be
     * generated based on the {@link FunctionalOperationContract} present for
     * the method, if any. If no such contract exists, a trivial Oracle is
     * generated with no inherent semantic value.
     * 
     * @param method
     *            the method
     * @return an Oracle for the method
     * @throws OracleGeneratorException
     */
    public Oracle createOracleForMethod(final KeYJavaMethod method)
            throws OracleGeneratorException {

        try {

            /*
             * Extract the postcondition of the method
             */
            final Term postCondition = method.getPostconditions().get(0);
            Term simplifiedPostCondition;

            /*
             * Simplify the postcondition
             */
            simplifiedPostCondition = this.oracleTermTransformer
                    .transform(postCondition);

            /*
             * Create and return the Oracle.
             */
            final Set<OracleClause> oracleClauses = new HashSet<OracleClause>();
            this.constructClause(simplifiedPostCondition, oracleClauses);

            return new Oracle(oracleClauses);

        } catch (final TermTransformerException e) {

            throw new OracleGeneratorException(e.getMessage());
        }
    }
}