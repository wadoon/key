package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.KeYStoneException;
import se.gu.svanefalk.testgeneration.keystone.equations.IComparator;
import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.Equals;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.GreaterOrEquals;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.LessOrEquals;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.Term;

public class ExpressionUtils {

    private static ExpressionUtils instance = null;

    public static ExpressionUtils getInstance() {

        if (ExpressionUtils.instance == null) {
            ExpressionUtils.instance = new ExpressionUtils();
        }
        return ExpressionUtils.instance;
    }

    private ExpressionUtils() {

    }


    /**
     * Negates an expression
     * 
     * @param expression
     *            the expression
     * @return the negated expression
     */
    public static void negate(IExpression expression) {

        /*
         * The expression is an addition - swap it to a subtraction, and negate
         * the lhand side.
         */
        if (expression instanceof Addition) {
            Addition addition = (Addition) expression;

            negate(addition.getLeftOperand());
            negate(addition.getRightOperand());
        }

        /*
         * The expression is a multiplication - keep it as it is, but negate the
         * lhand side.
         */
        else if (expression instanceof Multiplication) {
            Multiplication multiplication = (Multiplication) expression;

            negate(multiplication.getLeftOperand());
        }

        /*
         * The expression is a multiplication - keep it as it is, but negate the
         * lhand side.
         */
        else if (expression instanceof Division) {
            Division division = (Division) expression;

            negate(division.getLeftOperand());
        }

        /*
         * The expression is a numeric constant - swap its sign.
         */
        else if (expression instanceof NumericConstant) {
            NumericConstant constant = (NumericConstant) expression;
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
    public static void negateAddition(Addition addition)
            throws KeYStoneException {

        final IExpression rightOperand = addition.getRightOperand();

        if (rightOperand instanceof NumericConstant) {
            NumericConstant constant = (NumericConstant) rightOperand;
            negateConstant(constant);
        }

        else if (rightOperand instanceof Addition) {
            Addition additionChild = (Addition) rightOperand;

            IExpression additionLeftOperand = additionChild.getLeftOperand();
            if (additionLeftOperand instanceof NumericConstant) {
                NumericConstant constant = (NumericConstant) additionLeftOperand;
                negateConstant(constant);
            }

            else if (additionLeftOperand instanceof Variable) {
                Variable variable = (Variable) additionLeftOperand;
                negateVariable(variable);
            }
        }

        else if (rightOperand instanceof Multiplication) {
            Multiplication multiplication = (Multiplication) rightOperand;
            negateMultiplication(multiplication);
        }

        else {
            throw new KeYStoneException(
                    "Illegal operation in trying to negate addition");
        }
    }

    public static void negateMultiplication(Multiplication multiplication)
            throws KeYStoneException {

        final IExpression leftOperand = multiplication.getLeftOperand();

        if (leftOperand instanceof NumericConstant) {
            NumericConstant constant = (NumericConstant) leftOperand;
            negateConstant(constant);
        } else {
            throw new KeYStoneException(
                    "Illegal operation in trying to negate multiplication");
        }
    }

    public static void negateDivision(Division division)
            throws KeYStoneException {

        final IExpression leftOperand = division.getLeftOperand();

        if (leftOperand instanceof NumericConstant) {
            NumericConstant constant = (NumericConstant) leftOperand;
            negateConstant(constant);
        } else {
            throw new KeYStoneException(
                    "Illegal operation in trying to negate multiplication");
        }
    }

    public static void negateConstant(NumericConstant constant) {
        constant.setValue(constant.getValue().multiply(Fraction.MINUS_ONE));
    }

    public static void negateVariable(Variable variable) {
        variable.negate();
    }

    public static void negateSingleExpression(IExpression expression)
            throws KeYStoneException {

        if (expression instanceof Addition) {
            negateAddition((Addition) expression);
        }

        else if (expression instanceof NumericConstant) {
            negateConstant((NumericConstant) expression);
        }

        else if (expression instanceof Multiplication) {
            negateMultiplication((Multiplication) expression);
        }

        else if (expression instanceof Division) {
            negateDivision((Division) expression);
        }

        else if (expression instanceof Variable) {
            negateVariable((Variable) expression);
        }

        else {
            throw new KeYStoneException(
                    "Error when trying to negate an expression: no such expression: "
                            + expression);
        }
    }
}