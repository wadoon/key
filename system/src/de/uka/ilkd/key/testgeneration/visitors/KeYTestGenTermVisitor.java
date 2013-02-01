package de.uka.ilkd.key.testgeneration.visitors;

import java.util.HashMap;
import java.util.LinkedList;

import de.uka.ilkd.key.java.expression.operator.GreaterOrEquals;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.strategy.feature.TernarySumFeature;
import de.uka.ilkd.key.testgeneration.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelVariable;

/**
 * Used to define a custom set of {@link Term} visitors used in KeYTestGen.
 * 
 * @author christopher
 */
public abstract class KeYTestGenTermVisitor extends Visitor {

    /**
     * Used for storing an index over all primitive types currently handled by
     * KeYTestGen
     */
    protected static final LinkedList<String> primitiveTypes;

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
     * Check if the given term represents a program construct with a supported
     * primitive type as its base type, such as a method or local variable
     * declaration.
     * 
     * @param term
     *            the term to check
     * @return true if the Term represents an integer program construct, false
     *         otherwise
     */
    protected boolean isPrimitiveType(Term term) {

        String sortName = term.sort().name().toString();

        return primitiveTypes.contains(sortName);
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
     * @return true iff. the term represents a {@link SortDependingFunction}.
     */
    protected boolean isSortDependingFunction(Term term) {

        return term.op() instanceof SortDependingFunction;
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
    protected String resolveIdentifierString(Term term) {

        /*
         * Base case: underlying definition does not consist of any more nested
         * recursions, so we just extract the current variable name and go back.
         */
        if (term.op().getClass() == LocationVariable.class) {
            return getVariableNameForTerm(term);
        }

        /*
         * Recursive case: underlying definition is still recursively defined,
         * so keep unwinding it.
         */
        else if (term.toString().equals("null")) {
            return "null";
        } else {
            return resolveIdentifierString(term.sub(1)) + "_dot_"
                    + getVariableNameForTerm(term.sub(2));
        }
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
    protected String getVariableNameForTerm(Term term) {

        Operator operator = term.op();
        String name = operator.name().toString();

        String[] splitName = name.split("::\\$");
        return splitName[splitName.length - 1].replaceAll("[^A-Za-z0-9]", "");
    }
}