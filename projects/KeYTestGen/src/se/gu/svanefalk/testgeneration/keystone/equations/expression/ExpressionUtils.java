package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.KeYStoneException;
import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public class ExpressionUtils {

    private static ExpressionUtils instance = null;

    public static ExpressionUtils getInstance() {

        if (ExpressionUtils.instance == null) {
            ExpressionUtils.instance = new ExpressionUtils();
        }
        return ExpressionUtils.instance;
    }

    /**
     * Negates an expression
     * 
     * @param expression
     *            the expression
     * @return the negated expression
     */
    public static void negate(final IExpression expression) {

        /*
         * The expression is an addition - swap it to a subtraction, and negate
         * the lhand side.
         */
        if (expression instanceof Addition) {
            final Addition addition = (Addition) expression;

            ExpressionUtils.negate(addition.getLeftOperand());
            ExpressionUtils.negate(addition.getRightOperand());
        }

        /*
         * The expression is a multiplication - keep it as it is, but negate the
         * lhand side.
         */
        else if (expression instanceof Multiplication) {
            final Multiplication multiplication = (Multiplication) expression;

            ExpressionUtils.negate(multiplication.getLeftOperand());
        }

        /*
         * The expression is a multiplication - keep it as it is, but negate the
         * lhand side.
         */
        else if (expression instanceof Division) {
            final Division division = (Division) expression;

            ExpressionUtils.negate(division.getLeftOperand());
        }

        /*
         * The expression is a numeric constant - swap its sign.
         */
        else if (expression instanceof NumericConstant) {
            final NumericConstant constant = (NumericConstant) expression;
            constant.setValue(constant.getValue().multiply(Fraction.MINUS_ONE));
        }

        /*
         * The expression is a variable - simply negate it. //TODO: fix this
         */
        else if (expression instanceof Variable) {

            // TODO;
        }
    }

    /**
     * Negate an addition at one level only, i.e. turn 1 + 2 + 3 into 1 - 2 + 3
     * 
     * @param addition
     *            the operation
     * @throws KeYStoneException
     *             in case of an error
     */
    public static void negateAddition(final Addition addition)
            throws KeYStoneException {

        final IExpression rightOperand = addition.getRightOperand();

        if (rightOperand instanceof NumericConstant) {
            final NumericConstant constant = (NumericConstant) rightOperand;
            ExpressionUtils.negateConstant(constant);
        }

        else if (rightOperand instanceof Addition) {
            final Addition additionChild = (Addition) rightOperand;

            final IExpression additionLeftOperand = additionChild.getLeftOperand();
            if (additionLeftOperand instanceof NumericConstant) {
                final NumericConstant constant = (NumericConstant) additionLeftOperand;
                ExpressionUtils.negateConstant(constant);
            }

            else if (additionLeftOperand instanceof Variable) {
                final Variable variable = (Variable) additionLeftOperand;
                ExpressionUtils.negateVariable(variable);
            }
        }

        else if (rightOperand instanceof Multiplication) {
            final Multiplication multiplication = (Multiplication) rightOperand;
            ExpressionUtils.negateMultiplication(multiplication);
        }

        else {
            throw new KeYStoneException(
                    "Illegal operation in trying to negate addition");
        }
    }

    public static void negateConstant(final NumericConstant constant) {
        constant.setValue(constant.getValue().multiply(Fraction.MINUS_ONE));
    }

    public static void negateDivision(final Division division)
            throws KeYStoneException {

        final IExpression leftOperand = division.getLeftOperand();

        if (leftOperand instanceof NumericConstant) {
            final NumericConstant constant = (NumericConstant) leftOperand;
            ExpressionUtils.negateConstant(constant);
        } else {
            throw new KeYStoneException(
                    "Illegal operation in trying to negate multiplication");
        }
    }

    public static void negateMultiplication(final Multiplication multiplication)
            throws KeYStoneException {

        final IExpression leftOperand = multiplication.getLeftOperand();

        if (leftOperand instanceof NumericConstant) {
            final NumericConstant constant = (NumericConstant) leftOperand;
            ExpressionUtils.negateConstant(constant);
        } else {
            throw new KeYStoneException(
                    "Illegal operation in trying to negate multiplication");
        }
    }

    public static void negateSingleExpression(final IExpression expression)
            throws KeYStoneException {

        if (expression instanceof Addition) {
            ExpressionUtils.negateAddition((Addition) expression);
        }

        else if (expression instanceof NumericConstant) {
            ExpressionUtils.negateConstant((NumericConstant) expression);
        }

        else if (expression instanceof Multiplication) {
            ExpressionUtils.negateMultiplication((Multiplication) expression);
        }

        else if (expression instanceof Division) {
            ExpressionUtils.negateDivision((Division) expression);
        }

        else if (expression instanceof Variable) {
            ExpressionUtils.negateVariable((Variable) expression);
        }

        else {
            throw new KeYStoneException(
                    "Error when trying to negate an expression: no such expression: "
                            + expression);
        }
    }

    public static void negateVariable(final Variable variable) {
        variable.negate();
    }

    private ExpressionUtils() {

    }
}