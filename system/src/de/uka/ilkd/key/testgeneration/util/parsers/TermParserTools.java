package de.uka.ilkd.key.testgeneration.util.parsers;

import java.util.LinkedList;

import org.hamcrest.core.IsNull;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfExThenElse;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.testgeneration.core.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelVariable;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.TermTransformerException;

/**
 * This class contains utility methods for parsers which can be used to in
 * various ways process {@link Term}s in the process of test case generation.
 * 
 * @author christopher
 */
public final class TermParserTools {

    private static final String ADDITION = "add";

    private static final String AND = "and";

    /**
     * The sort names of the various binary functions represented in the KeY
     * {@link Term} hierarchy. Note that equality is not a part of this list,
     * since it is represented by its own operational type {@link Equality}.
     */
    private static final LinkedList<String> binaryFunctions;

    private static final String BOOLEAN = "boolean";

    private static final String BYTE = "byte";

    private static final String DIVISION = "div";

    private static final String EQUALS = "equals";
    private static final String EXCEPTION_BASE = "java.lang.Exception";
    /**
     * The sort names for various Java Exceptions, as they are modelled in
     * KeYTestGen
     */
    private static final LinkedList<String> exceptionSorts;

    private static final String FALSE = "FALSE";
    private static final String GREATER_OR_EQUALS = "geq";

    private static final String GREATER_THAN = "geq";
    private static final String INTEGER = "int";
    private static final String LESS_OR_EQUALS = "leq";
    private static final String LESS_THAN = "leq";
    /**
     * The sort names of the literal kinds supported by KeYTestGen.
     */
    private static final LinkedList<String> literals;

    private static final String LONG = "long";
    private static final String MULTIPLICATION = "mul";
    private static final String NEGATE_LITERAL = "neglit";
    private static final String NOT = "not";

    private static final String NUMBERS = "numbers";
    /**
     * Used for storing an index over all operator types currently handled by
     * KeYTestGen
     */
    private static final LinkedList<String> operators;

    private static final String OR = "or";

    /**
     * The names of the various primitive types in Java. As of the
     * implementation of this class (November 2012), KeY does not support
     * floating point types (i.e. <b>float</b> and <b>double</b>), and neither
     * does KeYTestGen2.
     */
    private static final LinkedList<String> primitiveTypes;
    private static final String RESULT = "result";
    private static final String SUBTRACTION = "sub";
    private static final String TRUE = "TRUE";

    /**
     * The sort names of the unary functions as supported by KeYTestGen.
     */
    private static final LinkedList<String> unaryFunctions;

    private static final String Z = "Z";

    static {

        primitiveTypes = new LinkedList<String>();
        TermParserTools.primitiveTypes.add(TermParserTools.INTEGER);
        TermParserTools.primitiveTypes.add(TermParserTools.BOOLEAN);
        TermParserTools.primitiveTypes.add(TermParserTools.LONG);
        TermParserTools.primitiveTypes.add(TermParserTools.BYTE);

        literals = new LinkedList<String>();
        TermParserTools.literals.add(TermParserTools.NUMBERS);

        unaryFunctions = new LinkedList<String>();
        TermParserTools.unaryFunctions.add(TermParserTools.Z);
        TermParserTools.unaryFunctions.add(TermParserTools.NEGATE_LITERAL);

        binaryFunctions = new LinkedList<String>();
        TermParserTools.binaryFunctions.add(TermParserTools.GREATER_OR_EQUALS);
        TermParserTools.binaryFunctions.add(TermParserTools.LESS_OR_EQUALS);
        TermParserTools.binaryFunctions.add(TermParserTools.GREATER_THAN);
        TermParserTools.binaryFunctions.add(TermParserTools.LESS_THAN);
        TermParserTools.binaryFunctions.add(TermParserTools.MULTIPLICATION);
        TermParserTools.binaryFunctions.add(TermParserTools.DIVISION);
        TermParserTools.binaryFunctions.add(TermParserTools.ADDITION);
        TermParserTools.binaryFunctions.add(TermParserTools.SUBTRACTION);

        operators = new LinkedList<String>();
        TermParserTools.operators.add(TermParserTools.AND);
        TermParserTools.operators.add(TermParserTools.OR);
        TermParserTools.operators.add(TermParserTools.NOT);
        TermParserTools.operators.add(TermParserTools.GREATER_OR_EQUALS);
        TermParserTools.operators.add(TermParserTools.LESS_OR_EQUALS);
        TermParserTools.operators.add(TermParserTools.GREATER_THAN);
        TermParserTools.operators.add(TermParserTools.LESS_THAN);
        TermParserTools.operators.add(TermParserTools.MULTIPLICATION);
        TermParserTools.operators.add(TermParserTools.DIVISION);
        TermParserTools.operators.add(TermParserTools.ADDITION);
        TermParserTools.operators.add(TermParserTools.SUBTRACTION);
        TermParserTools.operators.add(TermParserTools.EQUALS);

        exceptionSorts = new LinkedList<String>();
        TermParserTools.exceptionSorts.add(TermParserTools.EXCEPTION_BASE);
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

        String termString = term.toString();
        if (termString
                .equalsIgnoreCase("int::select(heap,self,de.uka.ilkd.key.testgeneration.targetmodels.ClassProxy::$instanceInt)")) {
            int x = 10;
        }

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

            if (isNullSort(term.sub(1))) {

                return TermParserTools.getVariableNameForTerm(term.sub(2));

            } else {

                return resolveIdentifierString(term.sub(1), separator)
                        + separator
                        + TermParserTools.getVariableNameForTerm(term.sub(2));
            }
        }
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
     * @param term
     *            the term
     * @return true iff. the term represents an AND junctor
     */
    public static boolean isAnd(final Term term) {

        return term.op().name().toString().equals(TermParserTools.AND);
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
        if (isNot(term)) {
            return false;
        }

        final de.uka.ilkd.key.logic.op.Operator operator = term.op();

        return (operator instanceof Junctor) || (operator instanceof Equality);
    }

    public static boolean isBoolean(final Term term) {
        return term.sort().name().toString().equals(TermParserTools.BOOLEAN);
    }

    public static boolean isBooleanConstant(final Term term)
            throws TermParserException {
        return isBooleanFalse(term) || isBooleanTrue(term);
    }

    public static boolean isBooleanFalse(final Term term)
            throws TermParserException {
        if (isBoolean(term)) {
            return term.op().name().toString().equals(TermParserTools.FALSE);
        } else {
            throw new TermTransformerException(
                    "Attempted to apply boolean operation to non-boolean literal");
        }
    }

    public static boolean isBooleanTrue(final Term term)
            throws TermTransformerException {
        if (isBoolean(term)) {
            return term.op().name().toString().equals(TermParserTools.TRUE);
        } else {
            throw new TermTransformerException(
                    "Attempted to apply boolean operation to non-boolean literal");
        }
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

        return TermParserTools.exceptionSorts.contains(term.sort().name()
                .toString());
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

        return term.op().name().toString()
                .equals(TermParserTools.GREATER_OR_EQUALS);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a GREATER_THAN operator
     */
    public static boolean isGreaterThan(final Term term) {

        return term.op().name().toString().equals(TermParserTools.GREATER_THAN);
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

        return term.op().name().toString()
                .equals(TermParserTools.LESS_OR_EQUALS);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a LESS_THAN operator
     */
    public static boolean isLessThan(final Term term) {

        return term.op().name().toString().equals(TermParserTools.LESS_THAN);
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

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a NOT junctor
     */
    public static boolean isNot(final Term term) {

        return term.op().name().toString().equals(TermParserTools.NOT);
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

        if (isBinaryFunction2(term)) {

            return term.op().name().toString().equals(TermParserTools.OR);

        } else {

            return false;
        }
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

    /**
     * @param term
     *            the term
     * @return true iff. the term represents the RESULT constant
     */
    public static boolean isResult(final Term term) {

        return term.op().name().equals(TermParserTools.RESULT);
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

    public static boolean isUnaryFunction(final Term term) {

        final String sortName = term.op().name().toString();

        return TermParserTools.unaryFunctions.contains(sortName);
    }

    public static boolean isVariable(final Term term) {

        final Operator operator = term.op();

        return (operator instanceof Function)
                || (operator instanceof ProgramVariable);
    }

    public static boolean translateToJavaBoolean(final Term term)
            throws TermParserException {
        if (isBoolean(term)) {
            return isBooleanTrue(term) ? true : false;
        } else {
            throw new TermTransformerException(
                    "Attempted to apply boolean operation to non-boolean literal");
        }
    }

    public static boolean isPrimitiveType(String type) {
        return primitiveTypes.contains(type);
    }
}
