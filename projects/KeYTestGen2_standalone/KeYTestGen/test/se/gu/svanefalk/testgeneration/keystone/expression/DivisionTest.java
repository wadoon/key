package se.gu.svanefalk.testgeneration.keystone.expression;

import junit.framework.Assert;

import org.apache.commons.math3.fraction.Fraction;
import org.junit.Test;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Division;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.NumericConstant;

public class DivisionTest {

    // **************************************************************************
    // The below tests simply test different kinds of Divisions of numeric
    // constants. **************************************************************

    @Test
    public void testDivideTwoPositives() {

        IExpression expression = new Division(new NumericConstant(10),
                new NumericConstant(5));

        Fraction expected = new Fraction(2);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testDivideThreePositives() {

        IExpression expression = new Division(new NumericConstant(10),
                new Division(new NumericConstant(5), new NumericConstant(15)));

        Fraction expected = new Fraction(30);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testDivideTwoNegatives() {

        IExpression expression = new Division(new NumericConstant(-10),
                new NumericConstant(-5));

        Fraction expected = new Fraction(2);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testDivideThreeNegatives() {

        IExpression expression = new Division(new NumericConstant(-10),
                new Division(new NumericConstant(-5), new NumericConstant(-15)));

        Fraction expected = new Fraction(-30);
        Fraction actual = expression.evaluate();        
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testDivideOnePositiveOneNegative() {

        IExpression expression = new Division(new NumericConstant(10),
                new NumericConstant(-5));

        Fraction expected = new Fraction(-2);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testDivideOneNegativeOnePositive() {

        IExpression expression = new Division(new NumericConstant(-10),
                new NumericConstant(5));

        Fraction expected = new Fraction(-2);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testDivideOnePositiveOneNegativeOnePositive() {

        IExpression expression = new Division(new NumericConstant(10),
                new Division(new NumericConstant(-5), new NumericConstant(15)));

        Fraction expected = new Fraction(-30);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testDivideOnePositiveOnePositiveOneNegative() {

        IExpression expression = new Division(new NumericConstant(10),
                new Division(new NumericConstant(5), new NumericConstant(-15)));

        Fraction expected = new Fraction(-30);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testDivideOnePositiveOneNegativeOneNegative() {

        IExpression expression = new Division(new NumericConstant(10),
                new Division(new NumericConstant(-5), new NumericConstant(-15)));

        Fraction expected = new Fraction(30);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testDivideOneNegativeOnePositiveOnePositive() {

        IExpression expression = new Division(new NumericConstant(-10),
                new Division(new NumericConstant(5), new NumericConstant(15)));

        Fraction expected = new Fraction(-30);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testDivideOneNegativeOnePositiveOneNegative() {

        IExpression expression = new Division(new NumericConstant(-10),
                new Division(new NumericConstant(5), new NumericConstant(-15)));

        Fraction expected = new Fraction(30);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }

    @Test
    public void testDivideOneNegativeOneNegativeOnePositive() {

        IExpression expression = new Division(new NumericConstant(-10),
                new Division(new NumericConstant(-5), new NumericConstant(15)));

        Fraction expected = new Fraction(30);
        Fraction actual = expression.evaluate();
        Assert.assertEquals(expected, actual);
    }
}
