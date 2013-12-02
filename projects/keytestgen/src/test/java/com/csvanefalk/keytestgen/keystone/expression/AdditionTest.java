package com.csvanefalk.keytestgen.keystone.expression;

import com.csvanefalk.keytestgen.keystone.equations.IExpression;
import com.csvanefalk.keytestgen.keystone.equations.expression.Addition;
import com.csvanefalk.keytestgen.keystone.equations.expression.NumericConstant;
import junit.framework.Assert;
import org.apache.commons.math3.fraction.Fraction;
import org.junit.Test;

public class AdditionTest {

    // **************************************************************************
    // The below tests simply test different kinds of additions of numeric
    // constants. **************************************************************

    @Test
    public void testAddTwoPositives() {

        IExpression expression = new Addition(new NumericConstant(10),
                new NumericConstant(5));

        Fraction expected = new Fraction(15);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testAddThreePositives() {

        IExpression expression = new Addition(new NumericConstant(10),
                new Addition(new NumericConstant(5), new NumericConstant(15)));

        Fraction expected = new Fraction(30);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testAddTwoNegatives() {

        IExpression expression = new Addition(new NumericConstant(-10),
                new NumericConstant(-5));

        Fraction expected = new Fraction(-15);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testAddThreeNegatives() {

        IExpression expression = new Addition(new NumericConstant(-10),
                new Addition(new NumericConstant(-5), new NumericConstant(-15)));

        Fraction expected = new Fraction(-30);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testAddOnePositiveOneNegative() {

        IExpression expression = new Addition(new NumericConstant(10),
                new NumericConstant(-5));

        Fraction expected = new Fraction(5);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testAddOneNegativeOnePositive() {

        IExpression expression = new Addition(new NumericConstant(-10),
                new NumericConstant(5));

        Fraction expected = new Fraction(-5);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testAddOnePositiveOneNegativeOnePositive() {

        IExpression expression = new Addition(new NumericConstant(10),
                new Addition(new NumericConstant(-5), new NumericConstant(15)));

        Fraction expected = new Fraction(20);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testAddOnePositiveOnePositiveOneNegative() {

        IExpression expression = new Addition(new NumericConstant(10),
                new Addition(new NumericConstant(5), new NumericConstant(-15)));

        Fraction expected = new Fraction(0);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testAddOnePositiveOneNegativeOneNegative() {

        IExpression expression = new Addition(new NumericConstant(10),
                new Addition(new NumericConstant(-5), new NumericConstant(-15)));

        Fraction expected = new Fraction(-10);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testAddOneNegativeOnePositiveOnePositive() {

        IExpression expression = new Addition(new NumericConstant(-10),
                new Addition(new NumericConstant(5), new NumericConstant(15)));

        Fraction expected = new Fraction(10);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testAddOneNegativeOnePositiveOneNegative() {

        IExpression expression = new Addition(new NumericConstant(-10),
                new Addition(new NumericConstant(5), new NumericConstant(-15)));

        Fraction expected = new Fraction(-20);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testAddOneNegativeOneNegativeOnePositive() {

        IExpression expression = new Addition(new NumericConstant(-10),
                new Addition(new NumericConstant(-5), new NumericConstant(15)));

        Fraction expected = new Fraction(0);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }
}
