package de.uka.ilkd.key.testgeneration.parsers;

import java.util.LinkedList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.testgeneration.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelVariable;

/**
 * Children of this class represent parsers which can be used to in various ways
 * process {@link Term}s in the process of test case generation.
 * 
 * @author christopher
 */
public abstract class AbstractTermParser {

    protected final static TermFactory termFactory = TermFactory.DEFAULT;

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
     * Used for storing an index over all operator types currently handled by
     * KeYTestGen
     */
    protected static final LinkedList<String> operators;

    protected static final String AND = "and";
    protected static final String OR = "or";
    protected static final String NOT = "not";

    protected static final String GREATER_OR_EQUALS = "geq";
    protected static final String LESS_OR_EQUALS = "leq";
    protected static final String GREATER_THAN = "geq";
    protected static final String LESS_THAN = "leq";
    protected static final String EQUALS = "equals";

    protected static final String MULTIPLICATION = "and";
    protected static final String DIVISION = "division";
    protected static final String ADDITION = "addition";
    protected static final String SUBTRACTION = "subtraction";

    protected static final String INTEGER = "int";
    protected static final String BOOLEAN = "boolean";
    protected static final String LONG = "long";
    protected static final String BYTE = "byte";

    protected static final String RESULT = "result";
    
    static {

        primitiveTypes = new LinkedList<String>();
        primitiveTypes.add(INTEGER);
        primitiveTypes.add(BOOLEAN);
        primitiveTypes.add(LONG);
        primitiveTypes.add(BYTE);

        binaryFunctions = new LinkedList<String>();
        binaryFunctions.add(GREATER_OR_EQUALS);
        binaryFunctions.add(LESS_OR_EQUALS);
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
    protected static String resolveIdentifierString(Term term) {

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

            return resolveIdentifierString(term.sub(1)) + "_dot_"
                    + getVariableNameForTerm(term.sub(2));
        }
    }
    
    
    /**
     * Check if the given Term represents a binary function, such as any of the
     * {@link Junctor} instances.
     * 
     * @param term
     * @return
     */
    protected boolean isBinaryFunction(Term term) {

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

        if (isBinaryFunction(term)) {

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

        if (isBinaryFunction(term)) {

            return term.sort() instanceof NullSort;

        } else {

            return false;
        }
    }

    /**
     * @param term
     *            the term
     * @return true iff. the term represents a {@link LocationVariable}
     */
    protected boolean isLocationVariable(Term term) {

        String sort = term.sort().name().toString();
        return term.op() instanceof LocationVariable
                || primitiveTypes.contains(sort);
    }
    
    /**
     * @param term
     *            the term
     * @return true iff. the term represents a {@link LocationVariable}
     */
    protected boolean isSortDependingFunction(Term term) {

        return term.op() instanceof SortDependingFunction;
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
}
