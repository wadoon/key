package se.gu.svanefalk.testgeneration.keystone.equations;

import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import javax.naming.OperationNotSupportedException;

import se.gu.svanefalk.testgeneration.keystone.equations.comparator.Equals;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.AbstractBinaryExpression;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.AbstractUnaryExpression;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Addition;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Division;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Multiplication;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Subtraction;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Variable;

/**
 * Instances of this class represent equations.
 * 
 * @author christopher
 * 
 */
public class Equation {

    /**
     * The root of the equation itself.
     */
    private final Equals root;

    /**
     * The variables present in the equation.
     */
    private final Set<Variable> variables;

    /**
     * @return the variables
     */
    public Set<Variable> getVariables() {
        return variables;
    }

    /**
     * Creates a new Equation from an expression tree and a set of variables.
     * 
     * @param root
     * @param variables
     */
    private Equation(Equals root, Set<Variable> variables) {
        super();
        this.root = root;
        this.variables = variables;
    }

    /**
     * Creates an Equation from a tree representation.
     * 
     * @param root
     * @return
     */
    public static Equation createEquation(Equals root) {

        Set<Variable> variables = extractVariables(root);
        return new Equation(root, variables);
    }

    /**
     * Creates a set of all variables in the equation.
     * 
     * @param root
     * @return
     */
    private static Set<Variable> extractVariables(Equals root) {

        Set<Variable> variables = new HashSet<>();

        extractVariables_helper(root.getLeftOperand(), variables);
        extractVariables_helper(root.getRightOperand(), variables);

        return variables;
    }

    /**
     * Helper for {@link #extractVariables(Equals)}.
     * 
     * @param expression
     * @param variables
     */
    private static void extractVariables_helper(IExpression expression,
            Set<Variable> variables) {

        if (expression instanceof Variable) {
            variables.add((Variable) expression);

        } else if (expression instanceof AbstractBinaryExpression) {

            AbstractBinaryExpression binaryExpression = (AbstractBinaryExpression) expression;
            extractVariables_helper(binaryExpression.getLeftOperand(),
                    variables);
            extractVariables_helper(binaryExpression.getRightOperand(),
                    variables);
        }
    }

    /**
     * Solves this equation in order to get a binding for the target variable.
     * <p>
     * This does not affect the structure of the equation.
     * 
     * @param variables
     */
    public IExpression solveForVariable(Variable variable) {

        /*
         * Build a trace to the variable in question.
         */
        Deque<IExpression> trace = buildTrace(root, variable);
        assert trace != null;

        /*
         * Determine which side of the equation the variable is on, and set up
         * appropriate pointers.
         */
        IExpression oppositeEquationTop = null;
        IExpression variableEquationTop = null;

        variableEquationTop = trace.poll();
        if (root.getLeftOperand() == variableEquationTop) {
            oppositeEquationTop = root.getRightOperand();
        } else {
            oppositeEquationTop = root.getLeftOperand();
        }

        while (!trace.isEmpty()) {

            /*
             * Additions commute, so either non-variable side of the operation
             * can be move to the other side of the equation.
             */
            if (variableEquationTop instanceof Addition) {

                Addition addition = (Addition) variableEquationTop;
                IExpression variableOperand = trace.poll();

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
                IExpression oldOppositeEquationSide = oppositeEquationTop;
                oppositeEquationTop = new Subtraction(oldOppositeEquationSide,
                        nonVariableOperand);

                variableEquationTop = variableOperand;
            }

            /*
             * Multiplications commute as well, so we transform the equation
             * through simple division in this case.
             */
            if (variableEquationTop instanceof Multiplication) {

                Multiplication multiplication = (Multiplication) variableEquationTop;
                IExpression variableOperand = trace.poll();

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
                IExpression oldOppositeEquationSide = oppositeEquationTop;
                oppositeEquationTop = new Division(oldOppositeEquationSide,
                        nonVariableOperand);

                variableEquationTop = variableOperand;
            }

            /*
             * Since subtractions do not commute, the order of the operands will
             * determine how the move is made.
             */
            if (variableEquationTop instanceof Subtraction) {

                Subtraction subtraction = (Subtraction) variableEquationTop;
                IExpression variableOperand = trace.poll();
                IExpression oldOppositeEquationSide = oppositeEquationTop;

                IExpression nonVariableOperand = null;

                /*
                 * If the operand not leading to the variable is the left-hand
                 * operand of the subtraction, we move it to the other side of
                 * the equation by subtracting it, just as we would in the case
                 * of addition.
                 */
                if (subtraction.getRightOperand() == variableOperand) {
                    nonVariableOperand = subtraction.getLeftOperand();
                    oppositeEquationTop = new Subtraction(
                            oldOppositeEquationSide, nonVariableOperand);
                }

                /*
                 * Conversely, if it is the right-hand operand, we move it by
                 * adding it to the other side.
                 */
                else {
                    nonVariableOperand = subtraction.getRightOperand();
                    oppositeEquationTop = new Addition(oldOppositeEquationSide,
                            nonVariableOperand);
                }

                variableEquationTop = variableOperand;
            }

            /*
             * Division do not commute either, and we resolve them by further
             * division or multiplication, depending on where the variable is
             * situated.
             */
            if (variableEquationTop instanceof Subtraction) {

                Subtraction subtraction = (Subtraction) variableEquationTop;
                IExpression variableOperand = trace.poll();
                IExpression oldOppositeEquationSide = oppositeEquationTop;

                IExpression nonVariableOperand = null;

                /*
                 * If the operand not leading to the variable is the left-hand
                 * operand (i.e. situated in the numerator), we move it by
                 * division.
                 */
                if (subtraction.getRightOperand() == variableOperand) {
                    nonVariableOperand = subtraction.getLeftOperand();
                    oppositeEquationTop = new Division(oldOppositeEquationSide,
                            nonVariableOperand);
                }

                /*
                 * If it is the right-hand operator (i.e. the denominator), we
                 * move it by multiplication instead.
                 */
                else {
                    nonVariableOperand = subtraction.getRightOperand();
                    oppositeEquationTop = new Multiplication(
                            oldOppositeEquationSide, nonVariableOperand);
                }

                variableEquationTop = variableOperand;
            }
        }

        return oppositeEquationTop;
    }

    /**
     * Constructs a trace of expressions from the root of an equation, down to a
     * given variable. Assumes the variable only occurs in one place.
     * 
     * @param node 
     * @param variable
     * @return
     */
    private Deque<IExpression> buildTrace(Equals node, Variable variable) {

        assert node != null;
        assert variable != null;

        LinkedList<IExpression> queue = new LinkedList<>();

        Deque<IExpression> leftBranch = buildTrace(node.getLeftOperand(),
                variable);
        if (!leftBranch.isEmpty()) {
            return append(queue, leftBranch);
        }

        Deque<IExpression> rightBranch = buildTrace(node.getRightOperand(),
                variable);
        if (!rightBranch.isEmpty()) {
            return append(queue, rightBranch);
        }

        assert queue.isEmpty();
        return queue;
    }


    /**
     * Constructs a trace of expressions from the root of an equation, down to a
     * given variable. Assumes the variable only occurs in one place.
     * 
     * @param node 
     * @param variable
     * @return
     */
    private Deque<IExpression> buildTrace(IExpression node, Variable variable) {

        assert node != null;
        assert variable != null;

        LinkedList<IExpression> queue = new LinkedList<>();

        if (node instanceof AbstractBinaryExpression) {

            AbstractBinaryExpression binaryExpression = (AbstractBinaryExpression) node;

            Deque<IExpression> leftBranch = buildTrace(
                    binaryExpression.getLeftOperand(), variable);
            if (!leftBranch.isEmpty()) {
                queue.add(node);
                return append(queue, leftBranch);
            }

            Deque<IExpression> rightBranch = buildTrace(
                    binaryExpression.getRightOperand(), variable);
            if (!rightBranch.isEmpty()) {
                queue.add(node);
                return append(queue, rightBranch);
            }

            assert queue.isEmpty();
            return queue;
        }

        if (node instanceof AbstractUnaryExpression) {

            AbstractUnaryExpression unaryExpression = (AbstractUnaryExpression) node;

            Deque<IExpression> branch = buildTrace(
                    unaryExpression.getOperand(), variable);
            if (!branch.isEmpty()) {
                queue.add(node);
                return append(queue, branch);
            }

            assert queue.isEmpty();
            return queue;
        }

        if (node instanceof Variable) {

            if (node == variable) {
                queue.add(variable);
                return queue;
            }

            assert queue.isEmpty();
            return queue;
        }

        assert queue.isEmpty();
        return queue;
    }

    private Deque<IExpression> append(Deque<IExpression> head,
            Deque<IExpression> tail) {

        assert head != null;
        assert tail != null;

        for (IExpression expression : tail) {
            head.addLast(expression);
        }
        return head;
    }

    @Override
    public String toString() {
        return root.toString();
    }

    public boolean evaluate() throws OperationNotSupportedException {
        return root.evaluate();
    }
}