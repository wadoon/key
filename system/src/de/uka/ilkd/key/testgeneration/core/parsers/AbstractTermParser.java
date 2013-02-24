package de.uka.ilkd.key.testgeneration.core.parsers;

import java.util.LinkedList;

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
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.TermTransformerException;

/**
 * Children of this class represent parsers which can be used to in various ways
 * process {@link Term}s in the process of test case generation.
 * 
 * @author christopher
 */
public abstract class AbstractTermParser {

    /**
     * The names of the various primitive types in Java. As of the
     * implementation of this class (November 2012), KeY does not support
     * floating point types (i.e. <b>float</b> and <b>double</b>), and neither
     * does KeYTestGen2.
     */
    protected static final LinkedList<String> primitiveTypes;

    /**
     * The sort names of the various binary functions represented in the KeY
     * {@link Term} hierarchy. Note that equality is not a part of this list,
     * since it is represented by its own operational type {@link Equality}.
     */
    protected static final LinkedList<String> binaryFunctions;

    /**
     * The sort names of the unary functions as supported by KeYTestGen.
     */
    protected static final LinkedList<String> unaryFunctions;

    /**
     * The sort names of the literal kinds supported by KeYTestGen.
     */
    protected static final LinkedList<String> literals;

    /**
     * The sort names for various Java Exceptions, as they are modelled in
     * KeYTestGen
     */
    protected static final LinkedList<String> exceptionSorts;

    /**
     * Used for storing an index over all operator types currently handled by
     * KeYTestGen
     */
    protected static final LinkedList<String> operators;

    protected static final String AND = "and";
    protected static final String OR = "or";
    protected static final String NOT = "not";

    protected static final String TRUE = "TRUE";
    protected static final String FALSE = "FALSE";

    protected static final String GREATER_OR_EQUALS = "geq";
    protected static final String LESS_OR_EQUALS = "leq";
    protected static final String GREATER_THAN = "geq";
    protected static final String LESS_THAN = "leq";
    protected static final String EQUALS = "equals";

    protected static final String MULTIPLICATION = "mul";
    protected static final String DIVISION = "div";
    protected static final String ADDITION = "add";
    protected static final String SUBTRACTION = "sub";

    protected static final String Z = "Z";
    protected static final String NEGATE_LITERAL = "neglit";

    protected static final String NUMBERS = "numbers";

    protected static final String INTEGER = "int";
    protected static final String BOOLEAN = "boolean";
    protected static final String LONG = "long";
    protected static final String BYTE = "byte";

    protected static final String EXCEPTION_BASE = "java.lang.Exception";

    protected static final String RESULT = "result";

    static {

        primitiveTypes = new LinkedList<String>();
        primitiveTypes.add(INTEGER);
        primitiveTypes.add(BOOLEAN);
        primitiveTypes.add(LONG);
        primitiveTypes.add(BYTE);

        literals = new LinkedList<String>();
        literals.add(NUMBERS);

        unaryFunctions = new LinkedList<String>();
        unaryFunctions.add(Z);
        unaryFunctions.add(NEGATE_LITERAL);

        binaryFunctions = new LinkedList<String>();
        binaryFunctions.add(GREATER_OR_EQUALS);
        binaryFunctions.add(LESS_OR_EQUALS);
        binaryFunctions.add(GREATER_THAN);
        binaryFunctions.add(LESS_THAN);
        binaryFunctions.add(MULTIPLICATION);
        binaryFunctions.add(DIVISION);
        binaryFunctions.add(ADDITION);
        binaryFunctions.add(SUBTRACTION);

        operators = new LinkedList<String>();
        operators.add(AND);
        operators.add(OR);
        operators.add(NOT);
        operators.add(GREATER_OR_EQUALS);
        operators.add(LESS_OR_EQUALS);
        operators.add(GREATER_THAN);
        operators.add(LESS_THAN);
        operators.add(MULTIPLICATION);
        operators.add(DIVISION);
        operators.add(ADDITION);
        operators.add(SUBTRACTION);
        operators.add(EQUALS);

        exceptionSorts = new LinkedList<String>();
        exceptionSorts.add(EXCEPTION_BASE);
    }

    /**
     * Extracts the name of a field, given a representation on the form:
     * <code>[package].[class]::$[field]</code>
     * 
     * @param string
     * @return
     */
    protected static String extractName(Term term) {

        String fullName = term.toString();
        int splitterIndex = fullName.lastIndexOf('$');

        if (splitterIndex == -1) {
            return term.toString();
        }

        return fullName.substring(splitterIndex + 1).replaceAll("[^A-Za-z0-9]",
                "");
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
    protected static boolean isPrimitiveType(Term term) {

        String sortName = term.sort().name().toString();

        return primitiveTypes.contains(sortName);
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
    protected static String resolveIdentifierString(Term term, String separator) {

        Operator operator = term.op();

        /*
         * Base case 1: underlying definition is a LocationVariable and hence
         * does not consist of any more nested recursions, so we just extract
         * the current variable name and go back.
         */
        if (operator.getClass() == LocationVariable.class) {

            String name = getVariableNameForTerm(term);
            return name;
            // return isPrimitiveType(term) ? "self_" + name : name;
        }

        /*
         * Base case 2: underlying definition is a Function, and hence either
         * represents the symbolic heap or the root object instance ("self"). In
         * this case we also cannot go any further. We are not interested in the
         * symbolic heap here, so we simply return the root name.
         */
        else if (operator.getClass() == Function.class
                && !operator.toString().equals("heap")) {

            return operator.toString();
        }

        /*
         * Recursive case: underlying definition is still recursively defined,
         * so keep unwinding it.
         */
        else {

            return resolveIdentifierString(term.sub(1), separator) + separator
                    + getVariableNameForTerm(term.sub(2));
        }
    }

    protected boolean isLiteral(Term term) {

        String sortName = term.sort().name().toString();

        return literals.contains(sortName);
    }

    protected boolean isUnaryFunction(Term term) {

        String sortName = term.op().name().toString();

        return unaryFunctions.contains(sortName);
    }

    protected boolean isBinaryFunction(Term term) {

        String sortName = term.op().name().toString();

        return binaryFunctions.contains(sortName);
    }

    /**
     * Check if the given Term represents a binary function, such as any of the
     * {@link Junctor} instances.
     * 
     * @param term
     * @return
     */
    protected boolean isBinaryFunction2(Term term) {

        /*
         * Since Not also qualifies as a junctor, albeit a unary one, check this
         * first.
         */
        if (isNot(term)) {
            return false;
        }

        de.uka.ilkd.key.logic.op.Operator operator = term.op();

        return operator instanceof Junctor || operator instanceof Equality;
    }

    protected boolean isVariable(Term term) {

        Operator operator = term.op();

        return operator instanceof Function
                || operator instanceof ProgramVariable;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents an AND junctor
     */
    protected boolean isAnd(Term term) {

        return term.op().name().toString().equals(AND);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a GEQ operator
     */
    protected boolean isGreaterOrEquals(Term term) {

        return term.op().name().toString().equals(GREATER_OR_EQUALS);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a GREATER_THAN operator
     */
    protected boolean isGreaterThan(Term term) {

        return term.op().name().toString().equals(GREATER_THAN);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a LEQ operator
     */
    protected boolean isLessOrEquals(Term term) {

        return term.op().name().toString().equals(LESS_OR_EQUALS);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a LESS_THAN operator
     */
    protected boolean isLessThan(Term term) {

        return term.op().name().toString().equals(LESS_THAN);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents an or junctor
     */
    protected boolean isOr(Term term) {

        if (isBinaryFunction2(term)) {

            return term.op().name().toString().equals(OR);

        } else {

            return false;
        }
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents an EQUALS junctor
     */
    protected boolean isEquals(Term term) {

        return term.op() instanceof Equality;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents the RESULT constant
     */
    protected boolean isResult(Term term) {

        return term.op().name().equals(RESULT);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a NOT junctor
     */
    protected boolean isNot(Term term) {

        return term.op().name().toString().equals(NOT);
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents the {@link NullSort}
     */
    protected boolean isNullSort(Term term) {

        return term.sort() instanceof NullSort;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a Java Exception
     */
    protected boolean isExceptionSort(Term term) {

        return exceptionSorts.contains(term.sort().name().toString());
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a {@link ProgramVariable}.
     */
    protected boolean isProgramVariable(Term term) {

        return term.op() instanceof ProgramVariable;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a {@link LocationVariable}.
     */
    protected boolean isLocationVariable(Term term) {

        return term.op() instanceof LocationVariable;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a {@link SortDependingFunction}
     */
    protected boolean isSortDependingFunction(Term term) {

        return term.op() instanceof SortDependingFunction;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a {@link Function}
     */
    protected boolean isFunction(Term term) {

        return term.op() instanceof Function;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a {@link Junctor}
     */
    protected boolean isJunctor(Term term) {

        return term.op() instanceof Junctor;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a {@link SortedOperator}, which is
     *         one of the two fundamental base sorts for Terms in KeY.
     */
    protected boolean isSortedOperator(Term term) {

        return term.op() instanceof SortedOperator;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents an {@link IfExThenElse} statement.
     */
    protected boolean isIfExThenElse(Term term) {

        return term.op() instanceof IfExThenElse;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents an {@link IfThenElse} statement.
     */
    protected boolean isIfThenElse(Term term) {

        return term.op() instanceof IfThenElse;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents an {@link ObserverFunction}
     *         construct.
     */
    protected boolean isObserverFunction(Term term) {

        return term.op() instanceof ObserverFunction;
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents aa {@link ProgramMethod}.
     */
    protected boolean isProgramMethod(Term term) {

        return term.op() instanceof ProgramMethod;
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
    protected static String getVariableNameForTerm(Term term) {

        Operator operator = term.op();
        String name = operator.name().toString();

        String[] splitName = name.split("::\\$");
        return splitName[splitName.length - 1].replaceAll("[^A-Za-z0-9]", "");
    }

    /**
     * @param term
     *            the Term to check
     * @return true if the term has children, false otherwise.
     */
    protected boolean hasChildren(Term term) {

        return term.subs().size() != 0;
    }

    protected boolean isBoolean(Term term) {
        return term.sort().name().toString().equals(BOOLEAN);
    }

    protected boolean isBooleanTrue(Term term) throws TermTransformerException {
        if (isBoolean(term)) {
            return term.op().name().toString().equals(TRUE);
        } else {
            throw new TermTransformerException(
                    "Attempted to apply boolean operation to non-boolean literal");
        }
    }

    protected boolean isBooleanConstant(Term term) throws TermParserException {
        return isBooleanFalse(term) || isBooleanTrue(term);
    }

    protected boolean isBooleanFalse(Term term) throws TermParserException {
        if (isBoolean(term)) {
            return term.op().name().toString().equals(FALSE);
        } else {
            throw new TermTransformerException(
                    "Attempted to apply boolean operation to non-boolean literal");
        }
    }

    protected boolean translateToJavaBoolean(Term term)
            throws TermParserException {
        if (isBoolean(term)) {
            return isBooleanTrue(term) ? true : false;
        } else {
            throw new TermTransformerException(
                    "Attempted to apply boolean operation to non-boolean literal");
        }
    }
}
