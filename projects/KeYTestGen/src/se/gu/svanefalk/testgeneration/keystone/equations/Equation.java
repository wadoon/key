package se.gu.svanefalk.testgeneration.keystone.equations;

import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import javax.naming.OperationNotSupportedException;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.KeYStoneException;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.Equals;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.GreaterOrEquals;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.LessOrEquals;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.AbstractBinaryExpression;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.AbstractUnaryExpression;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Addition;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Division;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.DummyVariable;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.ExpressionUtils;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.ITreeNode;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Multiplication;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.NumericConstant;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Variable;

/**
 * Instances of this class represent equations.
 * 
 * @author christopher
 * 
 */
public class Equation {

    /**
     * Used for dynamic searches in the tree
     */
    private static interface ICondition {

        public boolean check(IExpression expression);
    }

    private static class isConstant implements ICondition {

        @Override
        public boolean check(final IExpression expression) {

            if (expression instanceof NumericConstant) {

                /*
                 * Check so the constant is not a multiplier.
                 */
                final ITreeNode parent = expression.getParent();
                return ((parent instanceof Addition)
                        || (parent instanceof IComparator) || (parent == null));
            }

            return false;
        }
    }

    private static final ICondition isConstant = new isConstant();

    private static Equals createEqualityFromInequality(
            final IComparator comparator) {

        final DummyVariable dummyVariable = DummyVariable.createDummyVariable();

        /*
         * Add slack variable.
         */
        if (comparator instanceof LessOrEquals) {

            final IExpression leftOperand = ((LessOrEquals) comparator).getLeftOperand();
            final IExpression rightOperand = ((LessOrEquals) comparator).getRightOperand();

            final Addition slackAddition = new Addition(leftOperand,
                    dummyVariable);

            return new Equals(slackAddition, rightOperand);
        }

        /*
         * Add surplus variable.
         */
        if (comparator instanceof GreaterOrEquals) {

            final IExpression leftOperand = ((GreaterOrEquals) comparator).getLeftOperand();
            final IExpression rightOperand = ((GreaterOrEquals) comparator).getRightOperand();

            dummyVariable.negate();
            final Addition surplusSubtraction = new Addition(leftOperand,
                    dummyVariable);

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
    public static Equation createEquation(final IComparator root)
            throws KeYStoneException {

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
        final Equation equation = new Equation(equality, variables);

        /*
         * Bring the constant part of the equation to one side
         */
        equation.isolateConstantPart();

        /*
         * If the constant is negative, negate the equation.
         */
        return equation;

    }

    /**
     * Creates a set of all variables in the equation.
     * 
     * @param root
     * @return
     */
    private static Map<String, Variable> extractVariables(final Equals root) {

        final Map<String, Variable> variables = new HashMap<>();

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
    private static void extractVariables_helper(final IExpression expression,
            final Map<String, Variable> variables2) {

        if (expression instanceof Variable) {
            final Variable variable = (Variable) expression;
            variables2.put(variable.getName(), variable);

        } else if (expression instanceof AbstractBinaryExpression) {

            final AbstractBinaryExpression binaryExpression = (AbstractBinaryExpression) expression;
            Equation.extractVariables_helper(binaryExpression.getLeftOperand(),
                    variables2);
            Equation.extractVariables_helper(
                    binaryExpression.getRightOperand(), variables2);
        }
    }

    /**
     * The root of the equation itself.
     */
    private final Equals root;

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
        super();
        this.root = root;
        this.variables = variables;
    }

    private Deque<IExpression> append(final Deque<IExpression> head,
            final Deque<IExpression> tail) {

        assert head != null;
        assert tail != null;

        for (final IExpression expression : tail) {
            head.addLast(expression);
        }
        return head;
    }

    /**
     * Constructs a trace of expressions from the root of an equation, down to a
     * given variable. Assumes the variable only occurs in one place.
     * 
     * @param node
     * @param variable
     * @return
     */
    private Deque<IExpression> buildTrace(final Equals node,
            final ICondition condition) {

        assert node != null;
        assert condition != null;

        final LinkedList<IExpression> queue = new LinkedList<>();

        final Deque<IExpression> leftBranch = buildTrace(node.getLeftOperand(),
                condition);
        if (!leftBranch.isEmpty()) {
            return append(queue, leftBranch);
        }

        final Deque<IExpression> rightBranch = buildTrace(
                node.getRightOperand(), condition);
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
    private Deque<IExpression> buildTrace(final IExpression node,
            final ICondition condition) {

        assert node != null;
        assert condition != null;

        final LinkedList<IExpression> queue = new LinkedList<>();

        if (condition.check(node)) {
            queue.add(node);
            return queue;
        }

        if (node instanceof AbstractBinaryExpression) {

            final AbstractBinaryExpression binaryExpression = (AbstractBinaryExpression) node;

            final Deque<IExpression> leftBranch = buildTrace(
                    binaryExpression.getLeftOperand(), condition);
            if (!leftBranch.isEmpty()) {
                queue.add(node);
                return append(queue, leftBranch);
            }

            final Deque<IExpression> rightBranch = buildTrace(
                    binaryExpression.getRightOperand(), condition);
            if (!rightBranch.isEmpty()) {
                queue.add(node);
                return append(queue, rightBranch);
            }

            assert queue.isEmpty();
            return queue;
        }

        if (node instanceof AbstractUnaryExpression) {

            final AbstractUnaryExpression unaryExpression = (AbstractUnaryExpression) node;

            final Deque<IExpression> branch = buildTrace(
                    unaryExpression.getOperand(), condition);
            if (!branch.isEmpty()) {
                queue.add(node);
                return append(queue, branch);
            }

            assert queue.isEmpty();
            return queue;
        }

        assert queue.isEmpty();
        return queue;
    }

    public boolean evaluate() throws OperationNotSupportedException {
        return root.evaluate();
    }

    public Fraction getConstant() {

        // FIXME: Hack
        return root.getRightOperand().evaluate();
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

    private void isolateConstantPart() throws KeYStoneException {

        /*
         * Build a trace to the variable in question.
         */
        Deque<IExpression> trace = buildTrace(root, Equation.isConstant);
        if (trace.isEmpty() || (trace == null)) {
            root.setRightOperand(new Addition(root.getRightOperand(),
                    new NumericConstant(Fraction.ZERO)));
            trace = buildTrace(root, Equation.isConstant);
        }
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
                ExpressionUtils.negateSingleExpression(nonVariableOperand);
                oppositeEquationTop = new Addition(oldOppositeEquationSide,
                        nonVariableOperand);

                variableEquationTop = variableOperand;
            }
        }

        root.setLeftOperand(oppositeEquationTop);
        root.setRightOperand(variableEquationTop);
    }

    /**
     * Solves this equation in order to get a binding for the target variable.
     * <p>
     * This does not affect the structure of the equation.
     * 
     * @param variables
     * @throws KeYStoneException
     */
    public IExpression solveForVariable(final Variable variable)
            throws KeYStoneException {

        /*
         * Build a trace to the variable in question.
         */
        final Deque<IExpression> trace = buildTrace(root, null);
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
                oppositeEquationTop = new Addition(oldOppositeEquationSide,
                        nonVariableOperand);

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
                oppositeEquationTop = new Division(oldOppositeEquationSide,
                        nonVariableOperand);

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
                    oppositeEquationTop = new Division(oldOppositeEquationSide,
                            nonVariableOperand);
                }

                /*
                 * If it is the right-hand operator (i.e. the denominator), we
                 * move it by multiplication instead.
                 */
                else {
                    nonVariableOperand = division.getRightOperand();
                    oppositeEquationTop = new Multiplication(
                            oldOppositeEquationSide, nonVariableOperand);
                }

                variableEquationTop = variableOperand;
            }
        }

        return oppositeEquationTop;
    }

    @Override
    public String toString() {
        return root.toString();
    }
}