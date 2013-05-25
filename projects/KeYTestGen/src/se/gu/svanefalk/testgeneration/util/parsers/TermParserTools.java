package se.gu.svanefalk.testgeneration.util.parsers;

import java.util.LinkedList;

import se.gu.svanefalk.testgeneration.StringConstants;
import se.gu.svanefalk.testgeneration.core.model.implementation.Model;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelVariable;
import se.gu.svanefalk.testgeneration.util.transformers.TermTransformerException;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfExThenElse;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.NullSort;

/**
 * This class contains utility methods for parsers which can be used to in
 * various ways process {@link Term}s in the process of test case generation.
 * 
 * @author christopher
 */
public final class TermParserTools {

    /**
     * The sort names of the various binary functions represented in the KeY
     * {@link Term} hierarchy. Note that equality is not a part of this list,
     * since it is represented by its own operational type {@link Equality}.
     */
    private static final LinkedList<String> binaryFunctions;

    /**
     * The sort names for various Java Exceptions, as they are modelled in
     * KeYTestGen
     */
    private static final LinkedList<String> exceptionSorts;

    /**
     * The sort names of the literal kinds supported by KeYTestGen.
     */
    private static final LinkedList<String> literals;
    /**
     * Used for storing an index over all operator types currently handled by
     * KeYTestGen
     */
    private static final LinkedList<String> operators;
    /**
     * The names of the various primitive types in Java. As of the
     * implementation of this class (November 2012), KeY does not support
     * floating point types (i.e. <b>float</b> and <b>double</b>), and neither
     * does KeYTestGen2.
     */
    private static final LinkedList<String> primitiveTypes;
    /**
     * The names of the quantifiers supported by KeY: forall and exists
     */
    private static final LinkedList<String> quantifiers;

    /**
     * The sort names of the unary functions as supported by KeYTestGen.
     */
    private static final LinkedList<String> unaryFunctions;

    static {

        primitiveTypes = new LinkedList<String>();
        TermParserTools.primitiveTypes.add(StringConstants.INTEGER);
        TermParserTools.primitiveTypes.add(StringConstants.BOOLEAN);
        TermParserTools.primitiveTypes.add(StringConstants.LONG);
        TermParserTools.primitiveTypes.add(StringConstants.BYTE);

        literals = new LinkedList<String>();
        TermParserTools.literals.add(StringConstants.NUMBERS);

        unaryFunctions = new LinkedList<String>();
        TermParserTools.unaryFunctions.add(StringConstants.Z);
        TermParserTools.unaryFunctions.add(StringConstants.NEGATE_LITERAL);

        binaryFunctions = new LinkedList<String>();
        TermParserTools.binaryFunctions.add(StringConstants.GREATER_OR_EQUALS);
        TermParserTools.binaryFunctions.add(StringConstants.LESS_OR_EQUALS);
        TermParserTools.binaryFunctions.add(StringConstants.GREATER_THAN);
        TermParserTools.binaryFunctions.add(StringConstants.LESS_THAN);
        TermParserTools.binaryFunctions.add(StringConstants.MULTIPLICATION);
        TermParserTools.binaryFunctions.add(StringConstants.DIVISION);
        TermParserTools.binaryFunctions.add(StringConstants.ADDITION);
        TermParserTools.binaryFunctions.add(StringConstants.SUBTRACTION);

        operators = new LinkedList<String>();
        TermParserTools.operators.add(StringConstants.AND);
        TermParserTools.operators.add(StringConstants.OR);
        TermParserTools.operators.add(StringConstants.NOT);
        TermParserTools.operators.add(StringConstants.GREATER_OR_EQUALS);
        TermParserTools.operators.add(StringConstants.LESS_OR_EQUALS);
        TermParserTools.operators.add(StringConstants.GREATER_THAN);
        TermParserTools.operators.add(StringConstants.LESS_THAN);
        TermParserTools.operators.add(StringConstants.MULTIPLICATION);
        TermParserTools.operators.add(StringConstants.DIVISION);
        TermParserTools.operators.add(StringConstants.ADDITION);
        TermParserTools.operators.add(StringConstants.SUBTRACTION);
        TermParserTools.operators.add(StringConstants.EQUALS);
        TermParserTools.operators.add(StringConstants.IMPLIES);

        exceptionSorts = new LinkedList<String>();
        TermParserTools.exceptionSorts.add(StringConstants.EXCEPTION_BASE);

        quantifiers = new LinkedList<String>();
        TermParserTools.quantifiers.add(StringConstants.FORALL);
        TermParserTools.quantifiers.add(StringConstants.EXISTS);
    }

    /**
     * Extracts the name of a field, given a representation on the form:
     * <code>[package].[class]::$[field]</code>
     * 
     * @param string
     * @return
     */
    public static String extractName(final Term term) {

        final String fullName = term.toString();
        final int splitterIndex = fullName.lastIndexOf('$');

        if (splitterIndex == -1) {
            return term.toString();
        }

        return fullName.substring(splitterIndex + 1).replaceAll("[^A-Za-z0-9]",
                "");
    }

    /**
     * Retrieves the short-hand name of the variable a given Term represents.
     * For example, in the Term
     * 
     * <pre>
     * com.example.MyClass::$myVariable,
     * </pre>
     * 
     * the returned shorthand is <i>myVariable</i>.
     * 
     * @param term
     *            the Term to process
     * @return the short-hand name of the variable represented by the Term. If
     *         the Term does not represent a variable, the regular toString
     *         output of the Terms {@link Operator} instance is returned.
     */
    public static String getVariableNameForTerm(final Term term) {

        final Operator operator = term.op();
        final String name = operator.name().toString();

        final String[] splitName = name.split("::\\$");
        return splitName[splitName.length - 1].replaceAll("[^A-Za-z0-9]", "");
    }

    /**
     * @param term
     *            the Term to check
     * @return true if the term has children, false otherwise.
     */
    public static boolean hasChildren(final Term term) {

        return term.subs().size() != 0;
    }

    /**
     * 
     * @param term
     *            the term
     * @return if the term represents addition
     */
    public static boolean isAddition(final Term term) {
        return term.op().toString().equals(StringConstants.ADDITION);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents an AND junctor
     */
    public static boolean isAnd(final Term term) {

        return term.op().name().toString().equals(StringConstants.AND);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents an arithmetic comparator, i.e. GEQ,
     *         GREATER_THAN, LEQ, or LESS_THAN.
     */
    public static boolean isArithmeticComparator(final Term term) {

        return TermParserTools.isGreaterOrEquals(term)
                || TermParserTools.isGreaterThan(term)
                || TermParserTools.isLessOrEquals(term)
                || TermParserTools.isLessThan(term);
    }

    public static boolean isBinaryFunction(final Term term) {

        final String sortName = term.op().name().toString();

        return TermParserTools.binaryFunctions.contains(sortName);
    }

    /**
     * Check if the given Term represents a binary function, such as any of the
     * {@link Junctor} instances.
     * 
     * @param term
     * @return
     */
    public static boolean isBinaryFunction2(final Term term) {

        /*
         * Since Not also qualifies as a junctor, albeit a unary one, check this
         * first.
         */
        if (TermParserTools.isNot(term)) {
            return false;
        }

        final de.uka.ilkd.key.logic.op.Operator operator = term.op();

        return (operator instanceof Junctor) || (operator instanceof Equality);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term is of boolean type, false otherwise.
     */
    public static boolean isBoolean(final Term term) {
        return term.sort().name().toString().equals(StringConstants.BOOLEAN);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a boolean constant, false
     *         otherwise.
     */
    public static boolean isBooleanConstant(final Term term)
            throws TermParserException {
        return TermParserTools.isBooleanFalse(term)
                || TermParserTools.isBooleanTrue(term);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents the boolean constant FALSE, false
     *         otherwise.
     */
    public static boolean isBooleanFalse(final Term term)
            throws TermParserException {
        if (TermParserTools.isBoolean(term)) {
            return term.op().name().toString().equals(StringConstants.FALSE);
        } else {
            throw new TermTransformerException(
                    "Attempted to apply boolean operation to non-boolean literal");
        }
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents the boolean constant TRUE, false
     *         otherwise.
     */
    public static boolean isBooleanTrue(final Term term)
            throws TermTransformerException {
        if (TermParserTools.isBoolean(term)) {
            return term.op().name().toString().equals(StringConstants.TRUE);
        } else {
            throw new TermTransformerException(
                    "Attempted to apply boolean operation to non-boolean literal");
        }
    }

    /**
     * 
     * @param term
     *            the term
     * @return if the term represents division
     */
    public static boolean isDivision(final Term term) {
        return term.op().toString().equals(StringConstants.DIVISION);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents an EQUALS junctor
     */
    public static boolean isEquals(final Term term) {

        return term.op() instanceof Equality;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a Java Exception
     */
    public static boolean isExceptionSort(final Term term) {

        return TermParserTools.exceptionSorts.contains(term.sort().name().toString());
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents the EXISTS quantifier, false
     *         otherwise.
     */
    public static boolean isExistsQuantifier(final Term term) {

        return term.op().name().toString().equals(StringConstants.EXISTS);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents the FOR-ALL quantifier, false
     *         otherwise.
     */
    public static boolean isForAllQuantifier(final Term term) {

        return term.op().name().toString().equals(StringConstants.FORALL);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a Formula, false otherwise.
     */
    public static boolean isFormula(final Term term) {

        final String sortName = term.sort().name().toString();

        return sortName.equals("Formula");
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a {@link Function}
     */
    public static boolean isFunction(final Term term) {

        return term.op() instanceof Function;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a GEQ operator
     */
    public static boolean isGreaterOrEquals(final Term term) {

        return term.op().name().toString().equals(
                StringConstants.GREATER_OR_EQUALS);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a GREATER_THAN operator
     */
    public static boolean isGreaterThan(final Term term) {

        return term.op().name().toString().equals(StringConstants.GREATER_THAN);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents an {@link IfExThenElse} statement.
     */
    public static boolean isIfExThenElse(final Term term) {

        return term.op() instanceof IfExThenElse;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents an {@link IfThenElse} statement.
     */
    public static boolean isIfThenElse(final Term term) {

        return term.op() instanceof IfThenElse;
    }

    public static boolean isImplication(final Term term) {

        return term.op().name().toString().equals(StringConstants.IMPLIES);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a negative number, i.e. the Z
     *         function, false otherwise.
     */
    public static boolean isInteger(final Term term) {

        final String name = term.op().name().toString();

        return name.equals("Z");
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a negative number, i.e. the Z
     *         function, false otherwise.
     */
    public static boolean isIntegerNegation(final Term term) {

        final String name = term.op().name().toString();

        return name.equals("neglit");
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a {@link Junctor}
     */
    public static boolean isJunctor(final Term term) {

        return term.op() instanceof Junctor;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a LEQ operator
     */
    public static boolean isLessOrEquals(final Term term) {

        return term.op().name().toString().equals(
                StringConstants.LESS_OR_EQUALS);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a LESS_THAN operator
     */
    public static boolean isLessThan(final Term term) {

        return term.op().name().toString().equals(StringConstants.LESS_THAN);
    }

    public static boolean isLiteral(final Term term) {

        final String sortName = term.sort().name().toString();

        return TermParserTools.literals.contains(sortName);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a {@link LocationVariable}.
     */
    public static boolean isLocationVariable(final Term term) {

        return term.op() instanceof LocationVariable;
    }

    public static boolean isLogicVariable(final Term term) {

        return term.op() instanceof LogicVariable;
    }

    /**
     * 
     * @param term
     *            the term
     * @return if the term represents multiplication
     */
    public static boolean isMultiplication(final Term term) {
        return term.op().toString().equals(StringConstants.MULTIPLICATION);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a NOT junctor
     */
    public static boolean isNot(final Term term) {

        return term.op().name().toString().equals(StringConstants.NOT);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents the {@link NullSort}
     */
    public static boolean isNullSort(final Term term) {

        return term.sort() instanceof NullSort;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents an {@link ObserverFunction}
     *         construct.
     */
    public static boolean isObserverFunction(final Term term) {

        return term.op() instanceof ObserverFunction;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents an or junctor
     */
    public static boolean isOr(final Term term) {

        if (TermParserTools.isBinaryFunction2(term)) {

            return term.op().name().toString().equals(StringConstants.OR);

        } else {

            return false;
        }
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term is of a primitive type, false otherwise.
     */
    public static boolean isPrimitiveType(final String type) {
        return TermParserTools.primitiveTypes.contains(type);
    }

    /**
     * Check if the given term represents a program construct with a supported
     * primitive type as its base type, such as a method or local variable
     * declaration.
     * 
     * @param term
     *            the term to check
     * @return true if the Term represents an integer program construct, false
     *         otherwise
     */
    public static boolean isPrimitiveType(final Term term) {

        final String sortName = term.sort().name().toString();

        return TermParserTools.primitiveTypes.contains(sortName);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents aa {@link ProgramMethod}.
     */
    public static boolean isProgramMethod(final Term term) {

        return term.op() instanceof ProgramMethod;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a {@link ProgramVariable}.
     */
    public static boolean isProgramVariable(final Term term) {

        return term.op() instanceof ProgramVariable;
    }

    public static boolean isQuantifier(final Term term) {

        return term.op() instanceof Quantifier;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents the RESULT constant
     */
    public static boolean isResult(final Term term) {

        return term.op().name().equals(StringConstants.RESULT);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a {@link SortDependingFunction}
     */
    public static boolean isSortDependingFunction(final Term term) {

        return term.op() instanceof SortDependingFunction;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a {@link SortedOperator}, which is
     *         one of the two fundamental base sorts for Terms in KeY.
     */
    public static boolean isSortedOperator(final Term term) {

        return term.op() instanceof SortedOperator;
    }

    /**
     * 
     * @param term
     *            the term
     * @return if the term represents subtraction
     */
    public static boolean isSubtraction(final Term term) {
        return term.op().toString().equals(StringConstants.SUBTRACTION);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a unary function, false otherwise.
     */
    public static boolean isUnaryFunction(final Term term) {

        final String sortName = term.op().name().toString();

        return TermParserTools.unaryFunctions.contains(sortName);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a variable, false otherwise.
     */
    public static boolean isVariable(final Term term) {

        final Operator operator = term.op();

        return (operator instanceof Function)
                || (operator instanceof ProgramVariable);
    }

    /**
     * Generate an identifier String for a variable. Such an identifier is used
     * in order to uniquely distinguish an instance of a {@link ModelVariable}.
     * <p>
     * If the variable is defined by a {@link SortDependingFunction}, the
     * identifier will be generated by recursively exploring the nesting
     * hierarchy this variable is a part of.
     * 
     * @param term
     *            the {@link Term} representing the variable
     * @return the identifier String.
     * @see Model
     */
    public static String resolveIdentifierString(final Term term,
            final String separator) {

        final Operator operator = term.op();

        term.toString();

        /*
         * Base case 1: underlying definition is a LocationVariable and hence
         * does not consist of any more nested recursions, so we just extract
         * the current variable name and go back.
         */
        if (operator.getClass() == LocationVariable.class) {

            final String name = TermParserTools.getVariableNameForTerm(term);

            return name;
            // return isPrimitiveType(term) ? "self_" + name : name;
        }

        /*
         * Base case 2: underlying definition is a Function, and hence either
         * represents the symbolic heap or the root object instance ("self"). In
         * this case we also cannot go any further. We are not interested in the
         * symbolic heap here, so we simply return the root name.
         */
        else if ((operator.getClass() == Function.class)
                && !operator.toString().equals("heap")) {

            return "self";
        }

        /*
         * Recursive case: underlying definition is still recursively defined,
         * so keep unwinding it.
         */
        else {

            if (TermParserTools.isNullSort(term.sub(1))) {

                return TermParserTools.getVariableNameForTerm(term.sub(2));

            } else {

                return TermParserTools.resolveIdentifierString(term.sub(1),
                        separator)
                        + separator
                        + TermParserTools.getVariableNameForTerm(term.sub(2));
            }
        }
    }

    /**
     * @param term
     *            a term of boolean type
     * @return a boolean value corresponding to the value of the term.
     */
    public static boolean translateToJavaBoolean(final Term term)
            throws TermParserException {
        if (TermParserTools.isBoolean(term)) {
            return TermParserTools.isBooleanTrue(term) ? true : false;
        } else {
            throw new TermTransformerException(
                    "Attempted to apply boolean operation to non-boolean literal");
        }
    }
}
