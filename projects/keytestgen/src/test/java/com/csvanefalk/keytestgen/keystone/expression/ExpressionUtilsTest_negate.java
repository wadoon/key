package com.csvanefalk.keytestgen.keystone.expression;

import com.csvanefalk.keytestgen.keystone.equations.IExpression;
import com.csvanefalk.keytestgen.keystone.equations.expression.*;
import junit.framework.Assert;
import org.apache.commons.math3.fraction.Fraction;
import org.junit.Test;

public class ExpressionUtilsTest_negate {

    // Tests the negation of different hiearchies of addition operators.

    @Test
    public void testNegateAdditionTwoOperands() {
        IExpression expression = new Addition(new NumericConstant(10), new NumericConstant(5));

        ExpressionUtils.negate(expression);
        Fraction negatedValue = expression.evaluate();

        Fraction expected = new Fraction(-15);
        Assert.assertEquals(expected, negatedValue);
    }

    @Test
    public void testNegateAdditionThreeOperands() {

        // 10 + 15 + 5
        IExpression expression = new Addition(new NumericConstant(10), new Addition(new NumericConstant(15),
                                                                                    new NumericConstant(5)));

        // -10 - 15 - 5
        ExpressionUtils.negate(expression);

        Fraction negatedValue = expression.evaluate();

        Fraction expected = new Fraction(-30);
        Assert.assertEquals(expected, negatedValue);
    }

    @Test
    public void testNegateAdditionFourOperands() {

        // 5 + 15 + 15 + 25
        IExpression expression = new Addition(new NumericConstant(5), new Addition(new NumericConstant(15),
                                                                                   new Addition(new NumericConstant(15),
                                                                                                new NumericConstant(25))));

        // 5 - 15 - 15 - 25
        ExpressionUtils.negate(expression);

        Fraction negatedValue = expression.evaluate();

        Fraction expected = new Fraction(-60);
        Assert.assertEquals(expected, negatedValue);
    }

    // Tests the negation of different hiearchies of subtraction operators.

    @Test
    public void testNegateSubtractionTwoOperands() {
        IExpression expression = new Addition(new NumericConstant(10), new NumericConstant(-5));

        ExpressionUtils.negate(expression);
        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(-5);

        Assert.assertEquals(expected, negatedValue);
    }

    @Test
    public void testNegateSubtractionThreeOperands() {

        IExpression expression = new Addition(new NumericConstant(10), new Addition(new NumericConstant(-15),
                                                                                    new NumericConstant(-5)));

        ExpressionUtils.negate(expression);

        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(10);

        Assert.assertEquals(expected, negatedValue);
    }

    @Test
    public void testNegateSubtractionFourOperands() {

        // 5 - 15 - 15 - 25
        IExpression expression = new Addition(new NumericConstant(5), new Addition(new NumericConstant(-15),
                                                                                   new Addition(new NumericConstant(-15),
                                                                                                new NumericConstant(-25))));

        ExpressionUtils.negate(expression);

        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(50);

        Assert.assertEquals(expected, negatedValue);
    }

    // Tests the negation of different hiearchies of multiplication operators.

    @Test
    public void testNegateMultiplicationTwoOperands() {
        IExpression expression = new Multiplication(new NumericConstant(10), new NumericConstant(5));

        ExpressionUtils.negate(expression);
        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(-50);

        Assert.assertEquals(expected, negatedValue);
    }

    @Test
    public void testNegateMultiplicationThreeOperands() {

        IExpression expression = new Multiplication(new NumericConstant(10), new Multiplication(new NumericConstant(15),
                                                                                                new NumericConstant(5)));

        ExpressionUtils.negate(expression);

        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(-750);

        Assert.assertEquals(expected, negatedValue);
    }

    @Test
    public void testNegateMultiplicationFourOperands() {

        IExpression expression = new Multiplication(new NumericConstant(5), new Multiplication(new NumericConstant(15),
                                                                                               new Multiplication(new NumericConstant(
                                                                                                       15),
                                                                                                                  new NumericConstant(
                                                                                                                          25))));

        ExpressionUtils.negate(expression);

        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(-28125);

        Assert.assertEquals(expected, negatedValue);
    }

    // Tests the negation of different hiearchies of division operators.

    @Test
    public void testNegateDivisionTwoOperands() {
        IExpression expression = new Division(new NumericConstant(10), new NumericConstant(5));

        ExpressionUtils.negate(expression);
        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(-2);

        Assert.assertEquals(expected, negatedValue);
    }

    @Test
    public void testNegateDivisionThreeOperands() {

        IExpression expression = new Division(new NumericConstant(10), new Division(new NumericConstant(15),
                                                                                    new NumericConstant(5)));

        ExpressionUtils.negate(expression);

        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(-10, 3);

        Assert.assertEquals(expected, negatedValue);
    }

    @Test
    public void testNegateDivisionFourOperands() {

        IExpression expression = new Division(new NumericConstant(5), new Division(new NumericConstant(15),
                                                                                   new Division(new NumericConstant(15),
                                                                                                new NumericConstant(25))));

        ExpressionUtils.negate(expression);

        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(-1, 5);

        Assert.assertEquals(expected, negatedValue);
    }

    // Tests the negation of some mixed cases of operators.

    @Test
    public void testNegateAdditionSubtraction() {

        IExpression expression = new Addition(new NumericConstant(20), new Addition(new NumericConstant(15),
                                                                                    new NumericConstant(-15)));

        ExpressionUtils.negate(expression);

        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(-20);

        Assert.assertEquals(expected, negatedValue);
    }

    @Test
    public void testNegateSubtractionAddition() {

        IExpression expression = new Addition(new NumericConstant(10), new Addition(new NumericConstant(-15),
                                                                                    new NumericConstant(5)));

        ExpressionUtils.negate(expression);

        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(0);

        Assert.assertEquals(expected, negatedValue);
    }

    @Test
    public void testNegateMultiplicationDivision() {

        IExpression expression = new Multiplication(new NumericConstant(10), new Division(new NumericConstant(15),
                                                                                          new NumericConstant(5)));

        ExpressionUtils.negate(expression);

        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(-30);

        Assert.assertEquals(expected, negatedValue);
    }

    @Test
    public void testNegateDivisionMultiplication() {

        IExpression expression = new Division(new NumericConstant(10), new Multiplication(new NumericConstant(15),
                                                                                          new NumericConstant(5)));

        ExpressionUtils.negate(expression);

        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(-2, 15);

        Assert.assertEquals(expected, negatedValue);
    }

    @Test
    public void testNegateAdditionSubtractionMultiplicationDivision() {

        // 5 + (15 - (10 * (15/25))
        IExpression expression = new Addition(new NumericConstant(5), new Addition(new NumericConstant(15),
                                                                                   new Multiplication(new NumericConstant(
                                                                                           -10),
                                                                                                      new Division(new NumericConstant(
                                                                                                              15),
                                                                                                                   new NumericConstant(
                                                                                                                           25)))));

        ExpressionUtils.negate(expression);

        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(-14);

        Assert.assertEquals(expected, negatedValue);
    }

    @Test
    public void testNegateSubtractionAdditionMultiplicationDivision() {

        // 5 - (15 + (10 * (15/25))
        IExpression expression = new Addition(new NumericConstant(5), new Addition(new NumericConstant(-15),
                                                                                   new Multiplication(new NumericConstant(
                                                                                           10),
                                                                                                      new Division(new NumericConstant(
                                                                                                              15),
                                                                                                                   new NumericConstant(
                                                                                                                           25)))));

        ExpressionUtils.negate(expression);
        Fraction negatedValue = expression.evaluate();
        Fraction expected = new Fraction(4);

        Assert.assertEquals(expected, negatedValue);
    }

    // Tests the negation of some mixed cases of operators.
}
