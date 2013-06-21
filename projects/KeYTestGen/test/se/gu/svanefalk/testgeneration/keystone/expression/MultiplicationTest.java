package se.gu.svanefalk.testgeneration.keystone.expression;

import junit.framework.Assert;

import org.apache.commons.math3.fraction.Fraction;
import org.junit.Test;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Multiplication;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.NumericConstant;

public class MultiplicationTest {

    // **************************************************************************
    // The below tests simply test different kinds of Multiplications of numeric
    // constants. **************************************************************

    @Test
    public void testMultiplyTwoPositives() {

        IExpression expression = new Multiplication(new NumericConstant(10),
                new NumericConstant(5));

        Fraction expected = new Fraction(50);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testMultiplyThreePositives() {

        IExpression expression = new Multiplication(new NumericConstant(10),
                new Multiplication(new NumericConstant(5), new NumericConstant(15)));

        Fraction expected = new Fraction(750);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testMultiplyTwoNegatives() {

        IExpression expression = new Multiplication(new NumericConstant(-10),
                new NumericConstant(-5));

        Fraction expected = new Fraction(50);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testMultiplyThreeNegatives() {

        IExpression expression = new Multiplication(new NumericConstant(-10),
                new Multiplication(new NumericConstant(-5), new NumericConstant(-15)));

        Fraction expected = new Fraction(-750);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testMultiplyOnePositiveOneNegative() {

        IExpression expression = new Multiplication(new NumericConstant(10),
                new NumericConstant(-5));

        Fraction expected = new Fraction(-50);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testMultiplyOneNegativeOnePositive() {

        IExpression expression = new Multiplication(new NumericConstant(-10),
                new NumericConstant(5));

        Fraction expected = new Fraction(-50);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testMultiplyOnePositiveOneNegativeOnePositive() {

        IExpression expression = new Multiplication(new NumericConstant(10),
                new Multiplication(new NumericConstant(-5), new NumericConstant(15)));

        Fraction expected = new Fraction(-750);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testMultiplyOnePositiveOnePositiveOneNegative() {

        IExpression expression = new Multiplication(new NumericConstant(10),
                new Multiplication(new NumericConstant(5), new NumericConstant(-15)));

        Fraction expected = new Fraction(-750);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testMultiplyOnePositiveOneNegativeOneNegative() {

        IExpression expression = new Multiplication(new NumericConstant(10),
                new Multiplication(new NumericConstant(-5), new NumericConstant(-15)));

        Fraction expected = new Fraction(750);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testMultiplyOneNegativeOnePositiveOnePositive() {

        IExpression expression = new Multiplication(new NumericConstant(-10),
                new Multiplication(new NumericConstant(5), new NumericConstant(15)));

        Fraction expected = new Fraction(-750);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testMultiplyOneNegativeOnePositiveOneNegative() {

        IExpression expression = new Multiplication(new NumericConstant(-10),
                new Multiplication(new NumericConstant(5), new NumericConstant(-15)));

        Fraction expected = new Fraction(750);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testMultiplyOneNegativeOneNegativeOnePositive() {

        IExpression expression = new Multiplication(new NumericConstant(-10),
                new Multiplication(new NumericConstant(-5), new NumericConstant(15)));

        Fraction expected = new Fraction(750);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }
}
