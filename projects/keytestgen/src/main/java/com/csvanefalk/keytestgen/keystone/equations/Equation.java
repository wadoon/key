package com.csvanefalk.keytestgen.keystone.equations;

import com.csvanefalk.keytestgen.keystone.KeYStoneException;
import com.csvanefalk.keytestgen.keystone.equations.comparator.Equals;
import com.csvanefalk.keytestgen.keystone.equations.comparator.GreaterOrEquals;
import com.csvanefalk.keytestgen.keystone.equations.comparator.LessOrEquals;
import com.csvanefalk.keytestgen.keystone.equations.expression.*;
import org.apache.commons.math3.fraction.Fraction;

import java.util.Deque;
import java.util.HashMap;
import java.util.Map;

/**
 * Instances of this class represent equations.
 *
 * @author christopher
 */
public class Equation extends Equals {

    private static Equals createEqualityFromInequality(final IComparator comparator) {

        final DummyVariable dummyVariable = DummyVariable.createDummyVariable();

        /*
         * Add slack variable.
         */
        if (comparator instanceof LessOrEquals) {

            final IExpression leftOperand = ((LessOrEquals) comparator).getLeftOperand();
            final IExpression rightOperand = ((LessOrEquals) comparator).getRightOperand();

            final Addition slackAddition = new Addition(leftOperand, dummyVariable);

            return new Equals(slackAddition, rightOperand);
        }

        /*
         * Add surplus variable.
         */
        if (comparator instanceof GreaterOrEquals) {

            final IExpression leftOperand = ((GreaterOrEquals) comparator).getLeftOperand();
            final IExpression rightOperand = ((GreaterOrEquals) comparator).getRightOperand();

            dummyVariable.negate();
            final Addition surplusSubtraction = new Addition(leftOperand, dummyVariable);

            return new Equals(surplusSubtraction, rightOperand);
        }

        return (Equals) comparator;
    }

    /**
     * Creates an Equation from a tree representation.
     *
     * @param root
     * @return
     * @throws KeYStoneException
     */
    public static Equation createEquation(final IComparator root) throws KeYStoneException {

        assert (root != null);

        /*
         * If the root object is an inequality, convert it to an equality by
         * introducing extra variables. After that, construct the variable
         * index.
         */
        final Equals equality = Equation.createEqualityFromInequality(root);
        assert (equality.getLeftOperand() != null);
        assert (equality.getRightOperand() != null);

        final Map<String, Variable> variables = Equation.extractVariables(equality);
        Equation equation = new Equation(equality, variables);

        equation = EquationUtils.normalizeEquation(equation);
        return equation;
    }

    /**
     * Creates a set of all variables in the equation.
     *
     * @param root
     * @return
     */
    private static Map<String, Variable> extractVariables(final Equals root) {

        final Map<String, Variable> variables = new HashMap<String, Variable>();

        Equation.extractVariables_helper(root.getLeftOperand(), variables);
        Equation.extractVariables_helper(root.getRightOperand(), variables);

        return variables;
    }

    /**
     * Helper for {@link #extractVariables(Equals)}.
     *
     * @param expression
     * @param variables2
     */
    private static void extractVariables_helper(final IExpression expression, final Map<String, Variable> variables2) {

        if (expression instanceof Variable) {
            final Variable variable = (Variable) expression;
            variables2.put(variable.getName(), variable);

        } else if (expression instanceof AbstractBinaryExpression) {

            final AbstractBinaryExpression binaryExpression = (AbstractBinaryExpression) expression;
            Equation.extractVariables_helper(binaryExpression.getLeftOperand(), variables2);
            Equation.extractVariables_helper(binaryExpression.getRightOperand(), variables2);
        }
    }

    /**
     * The variables present in the equation.
     */
    private final Map<String, Variable> variables;

    /**
     * Creates a new Equation from an expression tree and a set of variables.
     *
     * @param root
     * @param variables
     */
    private Equation(final Equals root, final Map<String, Variable> variables) {
        super(root.getLeftOperand(), root.getRightOperand());
        this.variables = variables;
    }

    public Fraction getConstant() {

        // FIXME: Hack
        return getRightOperand().evaluate();
    }

    public Variable getVariable(final String id) {
        return variables.get(id);
    }

    /**
     * @return the variables
     */
    public Map<String, Variable> getVariables() {
        return variables;
    }

    /**
     * Solves this equation in order to get a binding for the target variable.
     * <p/>
     * This does not affect the structure of the equation.
     *
     * @param variables
     * @throws KeYStoneException
     */
    public IExpression solveForVariable(final Variable variable) throws KeYStoneException {

        /*
         * Build a trace to the variable in question.
         */
        final Deque<IExpression> trace = EquationUtils.buildTrace(this, null);
        assert trace != null;

        /*
         * Determine which side of the equation the variable is on, and set up
         * appropriate pointers.
         */
        IExpression oppositeEquationTop = null;
        IExpression variableEquationTop = null;

        variableEquationTop = trace.poll();
        if (this.getLeftOperand() == variableEquationTop) {
            oppositeEquationTop = this.getRightOperand();
        } else {
            oppositeEquationTop = this.getLeftOperand();
        }

        while (!trace.isEmpty()) {

            /*
             * Additions commute, so either non-variable side of the operation
             * can be move to the other side of the equation.
             */
            if (variableEquationTop instanceof Addition) {

                final Addition addition = (Addition) variableEquationTop;
                final IExpression variableOperand = trace.poll();

                /*
                 * Identify which operand does /not/ lead to the variable we
                 * wish to isolate.
                 */
                IExpression nonVariableOperand = null;
                if (addition.getLeftOperand() == variableOperand) {
                    nonVariableOperand = addition.getRightOperand();
                } else {
                    nonVariableOperand = addition.getLeftOperand();
                }

                /*
                 * Negate and move it to the opposite side of the equation.
                 */
                final IExpression oldOppositeEquationSide = oppositeEquationTop;
                ExpressionUtils.negateAddition((Addition) nonVariableOperand);
                oppositeEquationTop = new Addition(oldOppositeEquationSide, nonVariableOperand);

                variableEquationTop = variableOperand;
            }

            /*
             * Multiplications commute as well, so we transform the equation
             * through simple division in this case.
             */
            if (variableEquationTop instanceof Multiplication) {

                final Multiplication multiplication = (Multiplication) variableEquationTop;
                final IExpression variableOperand = trace.poll();

                /*
                 * Identify which operand does /not/ lead to the variable we
                 * wish to isolate.
                 */
                IExpression nonVariableOperand = null;
                if (multiplication.getLeftOperand() == variableOperand) {
                    nonVariableOperand = multiplication.getRightOperand();
                } else {
                    nonVariableOperand = multiplication.getLeftOperand();
                }

                /*
                 * Move the non-variable operands to the other side through
                 * division.
                 */
                final IExpression oldOppositeEquationSide = oppositeEquationTop;
                oppositeEquationTop = new Division(oldOppositeEquationSide, nonVariableOperand);

                variableEquationTop = variableOperand;
            }

            /*
             * Division do not commute either, and we resolve them by further
             * division or multiplication, depending on where the variable is
             * situated.
             */
            if (variableEquationTop instanceof Division) {

                final Division division = (Division) variableEquationTop;
                final IExpression variableOperand = trace.poll();
                final IExpression oldOppositeEquationSide = oppositeEquationTop;

                IExpression nonVariableOperand = null;

                /*
                 * If the operand not leading to the variable is the left-hand
                 * operand (i.e. situated in the numerator), we move it by
                 * division.
                 */
                if (division.getRightOperand() == variableOperand) {
                    nonVariableOperand = division.getLeftOperand();
                    oppositeEquationTop = new Division(oldOppositeEquationSide, nonVariableOperand);
                }

                /*
                 * If it is the right-hand operator (i.e. the denominator), we
                 * move it by multiplication instead.
                 */
                else {
                    nonVariableOperand = division.getRightOperand();
                    oppositeEquationTop = new Multiplication(oldOppositeEquationSide, nonVariableOperand);
                }

                variableEquationTop = variableOperand;
            }
        }

        return oppositeEquationTop;
    }
}