package se.gu.svanefalk.testgeneration.core.oracle;

import java.util.HashSet;
import java.util.Set;

import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaMethod;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.Oracle;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleAssertion;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleComparator;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleComparator.ComparatorType;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleConstraint;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleExpression;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleLiteral;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleMetaExtractor;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleMethodInvocation;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleQuantifier;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleQuantifier.QuantifierType;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleType;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserException;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import se.gu.svanefalk.testgeneration.util.transformers.TermTransformerException;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IfExThenElse;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

/**
 * This singleton provides an API for turning the postconditions of Java
 * methods, represented by KeY {@link Term} instances, into test oracles
 * represented by {@link Oracle} instances.
 * 
 * @author christopher
 */
public enum OracleGenerator {
    INSTANCE;

    private static final Oracle EMPTY_ORACLE;
    static {
        Set<OracleAssertion> assertions = new HashSet<OracleAssertion>();
        OracleConstraint constraints = new OracleConstraint(assertions);
        EMPTY_ORACLE = new Oracle(constraints, null);
    }

    /**
     * Transformer used in order to simplify postconditions, turning them into a
     * form which is suitable for oracle generation.
     */
    private final SimplifyPostconditionTransformer oracleTermTransformer = new SimplifyPostconditionTransformer();

    /**
     * Constructs a set of {@link OracleAssertion} instances from a {@link Term}
     * 
     * @param term
     *            the term
     * @param clauses
     *            buffer for the generated assertions
     * @throws OracleGeneratorException
     */
    private void constructAssertions(final Term term,
            final Set<OracleAssertion> clauses) throws OracleGeneratorException {

        /*
         * The clause to be constructed.
         */
        OracleAssertion clause = null;

        /*
         * Expressions belonging to the Clause.
         */
        final Set<OracleExpression> expressions = new HashSet<OracleExpression>();

        /*
         * If the term is itself an AND junctor, it will either join two
         * expressions, or another AND junctor and an expression.
         */
        if (TermParserTools.isAnd(term)) {

            /*
             * Since the formula is in CNF, all occurences of AND junctions will
             * be in direct parent-child relationships with one another.
             * 
             * We hence start by checking if either of the children is an AND
             * junctor. If either is, we recursively continue to construct
             * Conjunctions for that child, while at the same time completing
             * the Conjunction for the current node by resolving the expression
             * related to it, which will in this case be present in the other
             * child.
             * 
             * The base case is if neither of the children represent an
             * AND-node. In this case we simply resolve the expressions
             * represented by both children and return.
             */
            final Term firstChild = term.sub(0);
            final Term secondChild = term.sub(1);

            if (TermParserTools.isAnd(firstChild)) {
                constructAssertions(firstChild, clauses);
                constructExpressions(secondChild, expressions);
            } else if (TermParserTools.isAnd(secondChild)) {
                constructAssertions(secondChild, clauses);
                constructExpressions(firstChild, expressions);
            } else {
                constructExpressions(firstChild, expressions);
                constructExpressions(secondChild, expressions);
            }
        }

        /*
         * Otherwise, the term represents a single expression to be resolved
         * into a single OracleAssertion.
         */
        else {
            constructExpressions(term, expressions);
        }

        clause = new OracleAssertion(expressions);
        clauses.add(clause);
    }

    /**
     * Constructs an {@link OracleExpression} from a Term representing any of
     * the binary functions, including EQUALS (although this is not strictly in
     * agreement with the semantics of JavaDL, it makes sense in the concept of
     * plain Java, which is what we are targeting here).
     * 
     * @param term
     *            the term
     * @param negate
     *            flag whether or not the operation should be negated
     * @return the generated OracleExpression
     * @throws OracleGeneratorException
     */
    private OracleExpression constructExpressionFromBinaryFunction(
            final Term term, final boolean negate)
            throws OracleGeneratorException {

        /*
         * Retrieve a comparator for the OracleConstraint expression
         */
        final ComparatorType comparator = OracleTypeFactory.getComparatorType(
                term, negate);

        final OracleExpression firstOperand = constructExpressionFromTerm(
                term.sub(0), negate);

        final OracleExpression secondOperand = constructExpressionFromTerm(
                term.sub(1), negate);

        return new OracleComparator(comparator, firstOperand, secondOperand);
    }

    private OracleExpression constructExpressionFromFormula(final Term term,
            final boolean negate) {
        // TODO Auto-generated method stub
        return null;
    }

    /**
     * Constructs an {@link OracleExpression} from a Term representing a
     * Function. A Function in KeY is a rather broad concept encapsulating a
     * wide range of different classes of objects, so we process selectively
     * depending on the sort of this particular instance.
     * 
     * @param term
     *            the term
     * @param negate
     *            flag whether or not the operation should be negated
     * @return the generated OracleExpression
     * @throws OracleGeneratorException
     */
    private OracleExpression constructExpressionFromFunction(final Term term,
            final boolean negate) throws OracleGeneratorException {

        try {

            /*
             * Order is crucial for proper resolution here, as the precise,
             * legitimate parent-child relationships between various
             * Function-type terms are not excplicitly spelled out in terms of
             * type relationships.
             */
            if (TermParserTools.isNullSort(term)) {
                return null;
            }

            if (TermParserTools.isBinaryFunction(term)) {
                return constructExpressionFromBinaryFunction(term, negate);
            }

            if (TermParserTools.isUnaryFunction(term)) {
                return constructExpressionFromUnaryFunction(term, negate);
            }

            if (TermParserTools.isProgramMethod(term)) {
                return constructExpressionFromProgramMethod(term, negate);
            }

            if (TermParserTools.isFormula(term)) {
                return constructExpressionFromFormula(term, negate);
            }

            if (TermParserTools.isBooleanConstant(term)) {
                return constructExpressionFromVariable(term);
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
            final Term term, final boolean negate) {

        return null;
    }

    /**
     * Constructs an {@link OracleExpression} from a Term representing a
     * Junctor. In our case, since AND and OR are already taken care of, we only
     * deal with EQUALS and NOT here.
     * 
     * @param term
     *            the term
     * @param negate
     *            flag whether or not the operation should be negated
     * @return the generated OracleExpression
     * @throws OracleGeneratorException
     */
    private OracleExpression constructExpressionFromJunctor(final Term term,
            final boolean negate) throws OracleGeneratorException,
            OracleGeneratorException {

        if (TermParserTools.isNot(term)) {
            return constructExpressionFromTerm(term.sub(0), true);
        }

        throw new OracleGeneratorException("Unsupported Junctor: "
                + term.op().name());
    }

    /**
     * Constructs an {@link OracleExpression} from a Term representing a
     * ProgramMethod, that is, a method invocation of some sort.
     * 
     * @param term
     *            the term
     * @param negate
     *            flag whether or not the operation should be negated
     * @return the generated OracleExpression
     * @throws OracleGeneratorException
     */
    private OracleExpression constructExpressionFromProgramMethod(
            final Term term, final boolean negate)
            throws OracleGeneratorException {

        /*
         * Get the identifier for the method
         */
        final int lastColon = term.op().name().toString().lastIndexOf(':');
        final String identifier = term.op().name().toString().substring(
                lastColon + 1);

        /*
         * Construct the return type
         */
        final OracleType returnType = OracleTypeFactory.getOracleType(term);

        /*
         * Construct the parent object from which this method is being invoked.
         */
        final Term parentObjectTerm = term.sub(1);
        final OracleType type = OracleTypeFactory.getOracleType(parentObjectTerm);
        final String parentIdentifier = term.toString();
        final OracleLiteral parentObject = new OracleLiteral(type,
                parentIdentifier);

        /*
         * Construct the parameter list. Note that this corresponds to a
         * sequence of expressions - not the formal parameters of the method
         * itself.
         */
        final int bufferSize = term.subs().size();
        final OracleExpression[] parameters = new OracleExpression[bufferSize - 2];
        for (int i = 2; i < bufferSize; i++) {
            final Term parameterTerm = term.sub(i);
            parameters[i - 2] = constructExpressionFromTerm(parameterTerm,
                    negate);
        }

        return new OracleMethodInvocation(returnType, identifier, parentObject,
                parameters);
    }

    /**
     * Constructs an {@link OracleExpression} from a Term representing a
     * quantifier, i.e. either FOR-ALL or EXISTS. The bound formula of this
     * quantifier will be simplified to an additional constraint, which makes
     * things more convenient and does not change the semantics of the formula
     * itself.
     * 
     * @param term
     *            the term
     * @param negate
     *            flag whether or not the operation should be negated
     * @return the generated OracleExpression
     * @throws OracleGeneratorException
     */
    private OracleExpression constructExpressionFromQuantifier(final Term term,
            final boolean negate) throws OracleGeneratorException {

        /*
         * Resolve the type of the quantifier
         */
        final QuantifierType quantifierType = OracleTypeFactory.getQuantifierType(term);

        /*
         * Resolve the expression bounded by this quantifier
         */
        final OracleConstraint boundExpression = constructOracle(term.sub(0));

        /*
         * Construct the quantifiable variable
         */
        final QuantifiableVariable variable = term.boundVars().get(0);
        final String identifier = variable.name().toString();
        final OracleType type = OracleTypeFactory.getOracleType(variable);
        final OracleLiteral quantifiableVariable = new OracleLiteral(type,
                identifier);

        return new OracleQuantifier(quantifierType, quantifiableVariable,
                boundExpression);
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
            final Term term, final boolean negate)
            throws OracleGeneratorException {

        if (TermParserTools.isFunction(term)) {
            return constructExpressionFromFunction(term, negate);
        }

        if (TermParserTools.isEquals(term)) {
            return constructExpressionFromBinaryFunction(term, negate);
        }

        if (TermParserTools.isJunctor(term)) {
            return constructExpressionFromJunctor(term, negate);
        }

        if (TermParserTools.isProgramVariable(term)) {
            return constructExpressionFromVariable(term);
        }

        if (TermParserTools.isLogicVariable(term)) {
            return constructExpressionFromVariable(term);
        }

        if (TermParserTools.isQuantifier(term)) {
            return constructExpressionFromQuantifier(term, negate);
        }

        throw new OracleGeneratorException("Unsupported SortedOperator: "
                + term.op().name());
    }

    /**
     * Top level function for constructiong an {@link OracleExpression} from any
     * term.
     * 
     * @param term
     *            the term
     * @param negate
     *            flag whether or not the operation should be negated
     * @return the generated OracleExpression
     * @throws OracleGeneratorException
     */
    private OracleExpression constructExpressionFromTerm(final Term term,
            final boolean negate) throws OracleGeneratorException {

        if (TermParserTools.isSortedOperator(term)) {
            return constructExpressionFromSortedOperator(term, negate);

        } else if (TermParserTools.isIfExThenElse(term)) {
            return constructExpressionFromIfExThenElse(term, negate);

        }
        throw new OracleGeneratorException(
                "Attempting to construct OracleConstraint from corrupt Term. Expected SortedOperator or IfThenElse, but found "
                        + term.op().name());
    }

    /**
     * Constructs an {@link OracleExpression} from a Term representing a unary
     * function. In our case, these will almost exclusively be such functions
     * which represent numeric values.
     * 
     * @param term
     *            the term
     * @param negate
     *            flag whether or not the operation should be negated
     * @return the generated OracleExpression
     * @throws OracleGeneratorException
     */
    private OracleExpression constructExpressionFromUnaryFunction(
            final Term term, final boolean negate)
            throws OracleGeneratorException {

        if (TermParserTools.isIntegerNegation(term)) {
            final String value = "-" + resolveNumbers(term.sub(0));
            final OracleType type = OracleTypeFactory.getOracleType(term);
            return new OracleLiteral(type, value);
        }

        return null;
    }

    /**
     * Constructs an {@link OracleLiteral} from a {@link LocationVariable}.
     * 
     * @param term
     *            the term representing the variable
     * @return the literal
     */
    private OracleExpression constructExpressionFromVariable(final Term term) {

        final OracleType type = OracleTypeFactory.getOracleType(term);
        final String identifier = term.toString();
        return new OracleLiteral(type, identifier);

    }

    /**
     * Given a set of {@link Term} instances joined together with 0 or more
     * OR-junctors, this function will resolve this chain into a corresponding
     * set of {@link OracleExpression} instances.
     * 
     * @param term
     * @param expressions
     * @throws OracleGeneratorException
     */
    private void constructExpressions(final Term term,
            final Set<OracleExpression> expressions)
            throws OracleGeneratorException {

        /*
         * If the Term is an Or-term, resolve both sub-expressions recursively
         */
        if (TermParserTools.isOr(term)) {
            constructExpressions(term.sub(0), expressions);
            constructExpressions(term.sub(1), expressions);
        } else {

            final OracleExpression expression = constructExpressionFromTerm(
                    term, false);
            expressions.add(expression);
        }
    }

    /**
     * Constructs an {@link Oracle} instance from a Term. The Term is
     * recursively resolved in order to translate each subnode into a
     * corresponding Oracle abstraction.
     * 
     * @param term
     *            the term
     * @return the oracle
     * @throws OracleGeneratorException
     */
    private OracleConstraint constructOracle(final Term term)
            throws OracleGeneratorException {

        /*
         * Create and return the OracleConstraint.
         */
        final Set<OracleAssertion> oracleClauses = new HashSet<OracleAssertion>();
        constructAssertions(term, oracleClauses);

        return new OracleConstraint(oracleClauses);
    }

    /**
     * Creates a Test Oracle for the provided method. The Oracle will be
     * generated based on the {@link FunctionalOperationContract} present for
     * the method, if any. If no such contract exists, a trivial
     * OracleConstraint is generated with no inherent semantic value.
     * 
     * @param method
     *            the method
     * @return an OracleConstraint for the method
     * @throws OracleGeneratorException
     */
    public Oracle generateOracle(final KeYJavaMethod method)
            throws OracleGeneratorException {

        try {

            /*
             * Handle methods which have no postcondition at all, simply giving
             * them an empty oracle.
             */
            if (method.getPostconditions() == null) {
                return EMPTY_ORACLE;
            }

            /*
             * Extract the postcondition of the method
             */
            final Term postCondition = method.getPostconditions().get(0);
            if (postCondition == null
                    || postCondition.toString().equals("true")) {
                return EMPTY_ORACLE;
            }

            /*
             * Extract metadata about the poststate of the program (such as
             * expected exceptions).
             */
            final OracleMetaExtractor metaExtractor = new OracleMetaExtractor();
            postCondition.execPreOrder(metaExtractor);
            final OracleType expectedException = metaExtractor.getThrownException();

            /*
             * Simplify the postcondition
             */
            final Term simplifiedPostCondition = oracleTermTransformer.transform(postCondition);
            if (simplifiedPostCondition == null) {
                return EMPTY_ORACLE;
            }

            /*
             * Create the postcondition constraints model
             */
            final OracleConstraint constraints = constructOracle(simplifiedPostCondition);

            return new Oracle(constraints, expectedException);

        } catch (final TermTransformerException e) {

            throw new OracleGeneratorException(e.getMessage());
        }
    }

    /**
     * Resolves a {@link Term} representing a numeric constant function into a
     * corresponding String numeral. For example, Z(0(1(#))) becomes -10.
     * 
     * @param term
     *            the term
     * @return the string numeral
     */
    private String resolveNumbers(final Term term) {

        final String numberString = term.op().name().toString();

        if (numberString.equals("#")) {
            return "";
        } else {
            return resolveNumbers(term.sub(0)) + numberString;
        }

    }
}