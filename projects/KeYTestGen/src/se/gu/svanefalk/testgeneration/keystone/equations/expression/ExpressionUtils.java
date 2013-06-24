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
            Variable variable = (Variable) expression;
            variable.negate();
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

        if (isAddition(expression)) {
            ExpressionUtils.negateAddition((Addition) expression);
        }

        else if (isConstant(expression)) {
            ExpressionUtils.negateConstant((NumericConstant) expression);
        }

        else if (isMultiplication(expression)) {
            ExpressionUtils.negateMultiplication((Multiplication) expression);
        }

        else if (isDivision(expression)) {
            ExpressionUtils.negateDivision((Division) expression);
        }

        else if (isVariable(expression)) {
            ExpressionUtils.negateVariable((Variable) expression);
        }

        else {
            throw new KeYStoneException(
                    "Error when trying to negate an expression: no such expression: "
                            + expression);
        }
    }

    public static boolean isAddition(IExpression expression) {
        return expression instanceof Addition;
    }

    public static boolean isConstant(IExpression expression) {
        return expression instanceof NumericConstant;
    }

    public static boolean isMultiplication(IExpression expression) {
        return expression instanceof Multiplication;
    }

    public static boolean isDivision(IExpression expression) {
        return expression instanceof Division;
    }

    public static boolean isVariable(IExpression expression) {
        return expression instanceof Variable;
    }

    /**
     * Adds together all free constants in an expression
     * 
     * @param expression
     * @return
     */
    private static Fraction addAllConstants(IExpression expression) {

        if (expression instanceof Addition) {

            Addition addition = (Addition) expression;
            return addAllConstants(addition.getLeftOperand()).add(
                    addAllConstants(addition.getRightOperand()));
        }

        else if (expression instanceof NumericConstant) {

            NumericConstant constant = (NumericConstant) expression;
            return constant.evaluate();
        } else {

            return Fraction.ZERO;
        }
    }

    /**
     * Simplifies an expression.
     * 
     * @param expression
     * @return
     */
    public static IExpression simplifyExpression(IExpression expression) {

        IExpression cleanExpression = removeConstants(expression);
        Fraction sum = addAllConstants(expression);

        NumericConstant newConstant = new NumericConstant(sum);

        /*
         * The expression consists only of constants
         */
        if (cleanExpression == null) {
            return newConstant;
        } else {
            if (isZero(newConstant)) {
                return cleanExpression;
            } else {
                return new Addition(newConstant, cleanExpression);
            }
        }
    }

    public static boolean isZero(NumericConstant constant) {
        return constant.getValue().equals(Fraction.ZERO);
    }

    /**
     * Removes all constants from an expression.
     * 
     * @param expression
     * @return
     */
    private static IExpression removeConstants(IExpression expression) {

        if (expression instanceof Addition) {
            Addition addition = (Addition) expression;
            IExpression leftOperand = removeConstants(addition.getLeftOperand());
            IExpression rightOperand = removeConstants(addition.getRightOperand());

            if (leftOperand == null && rightOperand == null) {
                return null;
            }

            else if (leftOperand != null && rightOperand != null) {
                return addition;
            }

            else {
                return (leftOperand != null) ? leftOperand : rightOperand;
            }
        }

        else if (expression instanceof NumericConstant) {
            return null;
        } else {
            return expression;
        }
    }

    public boolean containsExpressionType(IExpression target, IExpression type) {

        if (target.getClass() == type.getClass()) {
            return true;
        }

        else if (isBinaryExpression(target)) {
            AbstractBinaryExpression binaryExpression = (AbstractBinaryExpression) target;
            return containsExpressionType(binaryExpression.getLeftOperand(),
                    type)
                    || containsExpressionType(
                            binaryExpression.getRightOperand(), type);
        }

        else if (isUnaryExpression(target)) {
            AbstractUnaryExpression unaryExpression = (AbstractUnaryExpression) target;
            return containsExpressionType(unaryExpression.getOperand(), type);
        }

        else {
            return false;
        }
    }

    public static boolean isBinaryExpression(IExpression expression) {
        return expression instanceof AbstractBinaryExpression;
    }

    public static boolean isUnaryExpression(IExpression expression) {
        return expression instanceof AbstractUnaryExpression;
    }

    /**
     * Negates a {@link Variable} instance.
     * 
     * @param variable
     */
    public static void negateVariable(final Variable variable) {
        variable.negate();
    }

    public static boolean isNegative(NumericConstant constant) {
        return constant.evaluate().doubleValue() < 0;
    }

    private ExpressionUtils() {

    }
}