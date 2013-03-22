package se.gu.svanefalk.testgeneration.core.oracle;

import java.util.HashSet;
import java.util.Set;

import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaMethod;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.Oracle;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleClause;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleComparator;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleComparator.ComparatorType;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleExpression;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleLiteral;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleType;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserException;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import se.gu.svanefalk.testgeneration.util.parsers.transformers.TermTransformerException;
import de.uka.ilkd.key.collection.ImmutableArray;
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
     * Transformer used in order to constructExpressionFrom {@link Term}
     * instances representing postconditions into a form suitable for turning
     * them into Oracles.
     */
    private final OracleTermTransformer oracleTermTransformer = new OracleTermTransformer();

    private void constructClause(final Term term,
            final Set<OracleClause> clauses) throws OracleGeneratorException {

        /*
         * The clause to be constructed.
         */
        OracleClause clause = null;

        /*
         * Expressions belonging to the Clause.
         */
        final Set<OracleExpression> expressions = new HashSet<OracleExpression>();

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
     * @return the constructExpressionFromed term
     */
    protected OracleExpression constructExpressionFromAnd(final Term term,
            final boolean negate) throws OracleGeneratorException {

        /*
         * final Term firstChild =
         * this.constructExpressionFromTerm(term.sub(0)); final Term secondChild
         * = this.constructExpressionFromTerm(term.sub(1));
         */
        return null;
    }

    private OracleExpression constructExpressionFromBinaryFunction(
            final Term term, boolean negate) throws OracleGeneratorException {

        /*
         * Retrieve a comparator for the Oracle expression
         */
        ComparatorType comparator = OracleGenerationTools.getOracleComparator(
                term, negate);

        OracleExpression firstOperand = constructExpressionFromTerm(
                term.sub(0), negate);

        OracleExpression secondOperand = constructExpressionFromTerm(
                term.sub(1), negate);

        OracleComparator numericComparator = new OracleComparator(comparator,
                firstOperand, secondOperand);

        return numericComparator;
    }

    private OracleExpression constructExpressionFromBooleanConstant(
            final Term term, boolean negate) {
        return null;
    }

    /**
     * Transforms a {@link Term} representing {@link Equality}.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleExpression constructExpressionFromEquals(final Term term,
            final boolean negate) throws OracleGeneratorException {
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
    private OracleExpression constructExpressionFromFunction(final Term term,
            boolean negate) throws OracleGeneratorException {

        try {

            /*
             * Order is crucial for proper resolution here, as the precise,
             * legitimate parent-child relationships between various
             * Function-type terms are not excplicitly spelled out in terms of
             * type relationships.
             */
            if (TermParserTools.isNullSort(term)) {
                return this.constructExpressionFromNull(term, negate);
            }

            if (TermParserTools.isSortDependingFunction(term)) {
                return this.constructExpressionFromSortDependentFunction(term,
                        negate);
            }

            if (TermParserTools.isBinaryFunction(term)) {
                return this.constructExpressionFromBinaryFunction(term, negate);
            }

            if (TermParserTools.isUnaryFunction(term)) {
                return this.constructExpressionFromUnaryFunction(term, negate);
            }

            if (TermParserTools.isLiteral(term)) {
                return this.constructExpressionFromLiteral(term, negate);
            }

            if (TermParserTools.isObserverFunction(term)) {
                return this.constructExpressionFromObserverFunction(term,
                        negate);

            }

            if (TermParserTools.isBooleanConstant(term)) {
                return this
                        .constructExpressionFromBooleanConstant(term, negate);
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
    private OracleExpression constructExpressionFromIfExThenElse(
            final Term term, boolean negate) {

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
    private OracleExpression constructExpressionFromIfThenElse(final Term term) {

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
    private OracleExpression constructExpressionFromJunctor(final Term term,
            final boolean negate) throws OracleGeneratorException,
            OracleGeneratorException {

        if (TermParserTools.isAnd(term)) {
            return this.constructExpressionFromAnd(term, negate);

        } else if (TermParserTools.isOr(term)) {
            return this.constructExpressionFromOr(term, negate);

        } else if (TermParserTools.isEquals(term)) {
            return this.constructExpressionFromEquals(term, negate);

        } else if (TermParserTools.isNot(term)) {
            return this.constructExpressionFromNot(term, negate);
        }

        else if (TermParserTools.isImplication(term)) {
            return this.constructExpressionFromImplication(term, negate);
        }

        throw new OracleGeneratorException("Unsupported Junctor: "
                + term.op().name());
    }

    private OracleExpression constructExpressionFromImplication(
            final Term term, final boolean negate)
            throws OracleGeneratorException {

        final OracleExpression newFirstChild = this
                .constructExpressionFromTerm(term.sub(0), negate);
        
        final OracleExpression newSecondChild = this
                .constructExpressionFromTerm(term.sub(1), negate);

        return null;
    }

    /**
     * Transforms a {@link Term} representing a Literal.
     * 
     * @param term
     * @return
     * @throws OracleGeneratorException
     */
    private OracleExpression constructExpressionFromLiteral(final Term term,
            boolean negate) throws OracleGeneratorException {

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
     * Constructs an {@link OracleLiteral} from a {@link LocationVariable}.
     * 
     * @param term
     *            the term representing the variable
     * @return the literal
     */
    private OracleExpression constructExpressionFromLocationVariable(
            final Term term) {

        OracleType type = OracleGenerationTools.getOracleType(term);
        String identifier = term.toString();
        return new OracleLiteral(type, identifier);

    }

    /**
     * Transforms a {@link Term} representing a the NOT junctor.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleExpression constructExpressionFromNot(final Term term,
            final boolean negate) throws OracleGeneratorException {

        return constructExpressionFromTerm(term.sub(0), true);
    }

    /**
     * Transforms a {@link Term} which represents a null element, i.e. it has
     * the sort {@link NullSort}.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleExpression constructExpressionFromNull(final Term term,
            final boolean negate) {

        return null;
    }

    /**
     * Transforms a {@link Term} representing an {@link ObserverFunction}.
     * 
     * @param term
     *            the term
     * @return the constructExpressionFromed term
     */
    private OracleExpression constructExpressionFromObserverFunction(
            final Term term, boolean negate) {

        if (TermParserTools.isProgramMethod(term)) {
            return this.constructExpressionFromProgramMethod(term, negate);
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
    private OracleExpression constructExpressionFromOr(final Term term,
            final boolean negate) throws OracleGeneratorException {
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
    private OracleExpression constructExpressionFromProgramMethod(
            final Term term, boolean negate) {

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
    private OracleExpression constructExpressionFromProgramVariable(
            final Term term, boolean negate) throws OracleGeneratorException {

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
    private OracleExpression constructExpressionFromSortDependentFunction(
            final Term term, boolean negate) {

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
    private OracleExpression constructExpressionFromSortedOperator(
            final Term term, boolean negate) throws OracleGeneratorException {

        if (TermParserTools.isFunction(term)) {
            return this.constructExpressionFromFunction(term, negate);
        }

        if (TermParserTools.isEquals(term)) {
            return this.constructExpressionFromBinaryFunction(term, negate);
        }

        if (TermParserTools.isJunctor(term)) {
            return this.constructExpressionFromJunctor(term, negate);
        }

        if (TermParserTools.isProgramVariable(term)) {
            return this.constructExpressionFromProgramVariable(term, negate);
        }

        if (TermParserTools.isLogicVariable(term)) {
            return this.constructExpressionFromLogicVariable(term, negate);
        }

        if (TermParserTools.isQuantifier(term)) {
            return this.constructExpressionFromQuantifier(term, negate);
        }

        throw new OracleGeneratorException("Unsupported SortedOperator: "
                + term.op().name());
    }

    private OracleExpression constructExpressionFromLogicVariable(
            final Term term, final boolean negate) {

        return null;
    }

    private OracleExpression constructExpressionFromQuantifier(final Term term,
            final boolean negate) throws OracleGeneratorException {

        if (TermParserTools.isExistsQuantifier(term)) {
            return this.constructExpressionFromExistsQuantifier(term, negate);
        }

        if (TermParserTools.isForAllQuantifier(term)) {
            return this.constructExpressionFromForAllQuantifier(term, negate);
        }

        throw new OracleGeneratorException("Unsupported quantifier: "
                + term.op().name());
    }

    private OracleExpression constructExpressionFromForAllQuantifier(
            final Term term, final boolean negate)
            throws OracleGeneratorException {

        final OracleExpression newChild = this.constructExpressionFromTerm(
                term.sub(0), negate);

        return null;
    }

    private OracleExpression constructExpressionFromExistsQuantifier(
            final Term term, final boolean negate)
            throws OracleGeneratorException {

        final OracleExpression newChild = this.constructExpressionFromTerm(
                term.sub(0), negate);

        return null;
    }

    private OracleExpression constructExpressionFromTerm(final Term term,
            final boolean negate) throws OracleGeneratorException {

        if (TermParserTools.isSortedOperator(term)) {
            return this.constructExpressionFromSortedOperator(term, negate);

        } else if (TermParserTools.isIfExThenElse(term)) {
            return this.constructExpressionFromIfExThenElse(term, negate);

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
    private OracleExpression constructExpressionFromUnaryFunction(
            final Term term, boolean negate) throws OracleGeneratorException {

        // final Term child = this.constructExpressionFromTerm(term.sub(0));

        return null;
    }

    private void constructExpressions(final Term term,
            final Set<OracleExpression> expressions)
            throws OracleGeneratorException {

        /*
         * If the Term is an Or-term, resolve both sub-expressions recursively
         */
        if (TermParserTools.isOr(term)) {
            this.constructExpressions(term.sub(0), expressions);
            this.constructExpressions(term.sub(1), expressions);
        } else {

            final OracleExpression expression = this
                    .constructExpressionFromTerm(term, false);
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

            /*
             * Simplify the postcondition
             */
            Term simplifiedPostCondition = this.oracleTermTransformer
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