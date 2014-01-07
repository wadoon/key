package com.csvanefalk.keytestgen.keystone.equations;

import com.csvanefalk.keytestgen.keystone.KeYStoneException;
import com.csvanefalk.keytestgen.keystone.equations.comparator.Equals;
import com.csvanefalk.keytestgen.keystone.equations.comparator.GreaterOrEquals;
import com.csvanefalk.keytestgen.keystone.equations.comparator.LessOrEquals;
import com.csvanefalk.keytestgen.keystone.equations.expression.*;
import com.csvanefalk.keytestgen.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.Term;
import org.apache.commons.math3.fraction.Fraction;

import java.util.Deque;
import java.util.LinkedList;
import java.util.Map;

public class EquationUtils {

    private static EquationUtils instance = null;

    public static IComparator constructRelation(final Term term) throws KeYStoneException {
        assert (term != null);

        try {

            final IExpression leftChild = EquationUtils.processTerm(term.sub(0));
            assert (leftChild != null);

            final IExpression rightChild = EquationUtils.processTerm(term.sub(1));
            assert (rightChild != null);

            if (TermParserTools.isEquals(term)) {
                return new Equals(leftChild, rightChild);
            } else if (TermParserTools.isGreaterOrEquals(term)) {
                return new GreaterOrEquals(leftChild, rightChild);
            } else if (TermParserTools.isLessOrEquals(term)) {
                return new LessOrEquals(leftChild, rightChild);
            }
        } catch (Exception e) {
            throw new KeYStoneException("Caught unhandled exception: " + e.getMessage());
        }

        throw new KeYStoneException("Illegal comparator: " + term);
    }

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
                return ((parent instanceof Addition) || (parent instanceof IComparator) || (parent == null));
            }

            return false;
        }
    }

    private static final ICondition isConstant = new isConstant();

    public static EquationUtils getInstance() {

        if (EquationUtils.instance == null) {
            EquationUtils.instance = new EquationUtils();
        }
        return EquationUtils.instance;
    }

    private static IExpression processBinaryFunction(final Term term) throws KeYStoneException {

        final IExpression leftChild = EquationUtils.processTerm(term.sub(0));
        final IExpression rightChild = EquationUtils.processTerm(term.sub(1));

        if (TermParserTools.isAddition(term)) {
            final Addition addition = new Addition(leftChild, rightChild);
            return addition;
        }

        /*
         * Subtraction requires case distinction depending on exactly what is
         * being subtracted.
         */
        if (TermParserTools.isSubtraction(term)) {
            final Addition addition = new Addition(leftChild, rightChild);
            ExpressionUtils.negateAddition(addition);
            return addition;
        }

        if (TermParserTools.isDivision(term)) {
            return new Division(leftChild, rightChild);
        }

        if (TermParserTools.isMultiplication(term)) {
            return new Multiplication(leftChild, rightChild);
        }

        throw new KeYStoneException("Illegal binary function: " + term);
    }

    private static IExpression processFunction(final Term term) throws KeYStoneException {

        if (TermParserTools.isBinaryFunction(term)) {
            return EquationUtils.processBinaryFunction(term);
        }

        if (TermParserTools.isUnaryFunction(term)) {
            return EquationUtils.processUnaryFunction(term);
        }

        throw new KeYStoneException("Unsupported Function: " + term.op().name());
    }

    private static IExpression processTerm(final Term term) throws KeYStoneException {

        if (TermParserTools.isFunction(term)) {
            return EquationUtils.processFunction(term);
        }

        if (TermParserTools.isProgramVariable(term)) {
            return EquationUtils.processVariable(term);
        }

        if (TermParserTools.isLogicVariable(term)) {
            return EquationUtils.processVariable(term);
        }

        throw new KeYStoneException("Illegal term: " + term);
    }

    private static IExpression processUnaryFunction(final Term term) throws KeYStoneException {

        if (TermParserTools.isInteger(term)) {
            if (TermParserTools.isIntegerNegation(term.sub(0))) {
                final int value = Integer.parseInt("-" + TermParserTools.resolveNumber(term.sub(0).sub(0)));
                return new NumericConstant(new Fraction(value));
            } else {
                final int value = Integer.parseInt(TermParserTools.resolveNumber(term.sub(0)));
                return new NumericConstant(new Fraction(value));
            }
        }
        throw new KeYStoneException("Illegal unary function: " + term);
    }

    private static IExpression processVariable(final Term term) {

        return new Variable(term.toString());
    }

    private EquationUtils() {

    }

    /**
     * Simplifies an inequality by introducing extra variables, effectively
     * turning it into an equality.
     *
     * @param comparator
     * @param variableIndex
     * @param dummyVariable
     * @return
     */
    public Equals createEqualityFromInequality(final IComparator comparator,
                                               final Map<String, Variable> variableIndex,
                                               final Variable dummyVariable) {

        /*
         * Add slack variable.
         */
        if (comparator instanceof LessOrEquals) {

            final IExpression leftOperand = ((LessOrEquals) comparator).getLeftOperand();
            final IExpression rightOperand = ((LessOrEquals) comparator).getRightOperand();

            final Addition slackAddition = new Addition(leftOperand, dummyVariable);

            variableIndex.put(dummyVariable.getName(), dummyVariable);

            return new Equals(slackAddition, rightOperand);
        }

        /*
         * Add surplus variable.
         */
        if (comparator instanceof GreaterOrEquals) {

            dummyVariable.negate();

            final IExpression leftOperand = ((GreaterOrEquals) comparator).getLeftOperand();
            final IExpression rightOperand = ((GreaterOrEquals) comparator).getRightOperand();

            variableIndex.put(dummyVariable.getName(), dummyVariable);

            final Addition surplusSubtraction = new Addition(leftOperand, dummyVariable);

            return new Equals(surplusSubtraction, rightOperand);
        }

        return (Equals) comparator;
    }

    public static Equation simplifyEquation(Equation equation) throws KeYStoneException {

        /*
         * Simplify both sides of the equation.
         */
        IExpression simplifiedLeftHand = ExpressionUtils.simplifyExpression(equation.getLeftOperand());
        IExpression simplifiedRightHand = ExpressionUtils.simplifyExpression(equation.getRightOperand());

        /*
         * Isolate all constants to one side.
         */
        if (containsConstant(simplifiedLeftHand)) {

            if (ExpressionUtils.isConstant(simplifiedLeftHand)) {

                simplifiedRightHand = new Addition(simplifiedLeftHand, simplifiedRightHand);
                simplifiedRightHand = ExpressionUtils.simplifyExpression(simplifiedRightHand);

                simplifiedLeftHand = new NumericConstant(Fraction.ZERO);
            } else if (ExpressionUtils.isAddition(simplifiedLeftHand)) {
                Addition addition = (Addition) simplifiedLeftHand;

                /*
                 * In the addition, isolate which operand represents the
                 * constant, and which one represents the rest of the
                 * expression.
                 */
                IExpression target = null;
                IExpression other = null;
                if (ExpressionUtils.isConstant(addition.getLeftOperand())) {
                    target = addition.getLeftOperand();
                    other = addition.getRightOperand();
                } else {
                    target = addition.getRightOperand();
                    other = addition.getLeftOperand();
                }

                simplifiedLeftHand = other;
                simplifiedRightHand = new Addition(target, simplifiedRightHand);
                simplifiedRightHand = ExpressionUtils.simplifyExpression(simplifiedRightHand);
            }
        }

        /*
         * Modify and return the equation itself.
         */
        equation.setLeftOperand(simplifiedLeftHand);
        equation.setRightOperand(simplifiedRightHand);
        isolateConstantPart(equation);
        int x = 1;
        return equation;
    }

    public static Equation normalizeEquation(Equation equation) throws KeYStoneException {

        equation = simplifyEquation(equation);

        /*
         * Make sure that the constant part of the equation is positive.
         */
        NumericConstant constant = (NumericConstant) equation.getRightOperand();
        if (ExpressionUtils.isNegative(constant)) {
            equation = negateEquation(equation);
        }

        return equation;
    }

    public static Equation negateEquation(Equation equation) {
        ExpressionUtils.negate(equation.getLeftOperand());
        ExpressionUtils.negate(equation.getRightOperand());
        return equation;
    }

    /**
     * Check if a simplified expression contains a constant.
     *
     * @param expression
     * @return
     */
    private static boolean containsConstant(IExpression expression) {
        expression = ExpressionUtils.simplifyExpression(expression);

        if (ExpressionUtils.isConstant(expression)) {
            return true;
        } else if (ExpressionUtils.isAddition(expression)) {
            Addition addition = (Addition) expression;
            return ExpressionUtils.isConstant(addition.getLeftOperand()) || ExpressionUtils.isConstant(addition.getRightOperand());
        } else {
            return false;
        }
    }

    public static void isolateConstantPart(Equation equation) throws KeYStoneException {

        /*
         * Build a trace to the variable in question.
         */
        Deque<IExpression> trace = buildTrace(equation, isConstant);
        if (trace.isEmpty() || (trace == null)) {
            equation.setRightOperand(new Addition(equation.getRightOperand(), new NumericConstant(Fraction.ZERO)));
            trace = buildTrace(equation, isConstant);
        }
        assert trace != null;

        /*
         * Determine which side of the equation the variable is on, and set up
         * appropriate pointers.
         */
        IExpression oppositeEquationTop = null;
        IExpression variableEquationTop = null;

        variableEquationTop = trace.poll();
        if (equation.getLeftOperand() == variableEquationTop) {
            oppositeEquationTop = equation.getRightOperand();
        } else {
            oppositeEquationTop = equation.getLeftOperand();
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
                oppositeEquationTop = new Addition(oldOppositeEquationSide, nonVariableOperand);

                variableEquationTop = variableOperand;
            }
        }

        equation.setLeftOperand(oppositeEquationTop);
        equation.setRightOperand(variableEquationTop);
    }

    /**
     * Constructs a trace of expressions from the root of an equation, down to a
     * given variable. Assumes the variable only occurs in one place.
     *
     * @param node
     * @param condition
     * @return
     */
    public static Deque<IExpression> buildTrace(final Equation node, final ICondition condition) {

        assert node != null;
        assert condition != null;

        final LinkedList<IExpression> queue = new LinkedList<IExpression>();

        final Deque<IExpression> leftBranch = buildTrace(node.getLeftOperand(), condition);
        if (!leftBranch.isEmpty()) {
            return append(queue, leftBranch);
        }

        final Deque<IExpression> rightBranch = buildTrace(node.getRightOperand(), condition);
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
     * @param condition
     * @return
     */
    private static Deque<IExpression> buildTrace(final IExpression node, final ICondition condition) {

        assert node != null;
        assert condition != null;

        final LinkedList<IExpression> queue = new LinkedList<IExpression>();

        if (condition.check(node)) {
            queue.add(node);
            return queue;
        }

        if (node instanceof AbstractBinaryExpression) {

            final AbstractBinaryExpression binaryExpression = (AbstractBinaryExpression) node;

            final Deque<IExpression> leftBranch = buildTrace(binaryExpression.getLeftOperand(), condition);
            if (!leftBranch.isEmpty()) {
                queue.add(node);
                return append(queue, leftBranch);
            }

            final Deque<IExpression> rightBranch = buildTrace(binaryExpression.getRightOperand(), condition);
            if (!rightBranch.isEmpty()) {
                queue.add(node);
                return append(queue, rightBranch);
            }

            assert queue.isEmpty();
            return queue;
        }

        if (node instanceof AbstractUnaryExpression) {

            final AbstractUnaryExpression unaryExpression = (AbstractUnaryExpression) node;

            final Deque<IExpression> branch = buildTrace(unaryExpression.getOperand(), condition);
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

    private static Deque<IExpression> append(final Deque<IExpression> head, final Deque<IExpression> tail) {

        assert head != null;
        assert tail != null;

        for (final IExpression expression : tail) {
            head.addLast(expression);
        }
        return head;
    }
}
