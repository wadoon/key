package se.gu.svanefalk.testgeneration.keystone.expression;

import junit.framework.Assert;

import org.apache.commons.math3.fraction.Fraction;
import org.junit.Test;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Addition;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Division;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.ExpressionUtils;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Multiplication;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.NumericConstant;

public class ExpressionUtilsTest_simplifyExpression {

    @Test
    public void testSimplifyAdditionTwoOperands() {
        IExpression expression = new Addition(new NumericConstant(10),
                new NumericConstant(5));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof NumericConstant);

        Fraction expected = new Fraction(15);
        Assert.assertEquals(expected, simplifiedValue);
    }

    @Test
    public void testSimplifyAdditionThreeOperands() {

        IExpression expression = new Addition(new NumericConstant(10),
                new Addition(new NumericConstant(15), new NumericConstant(5)));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof NumericConstant);

        Fraction expected = new Fraction(30);
        Assert.assertEquals(expected, simplifiedValue);
    }

    @Test
    public void testSimplifyAdditionFourOperands() {

        IExpression expression = new Addition(new NumericConstant(5),
                new Addition(new NumericConstant(15), new Addition(
                        new NumericConstant(15), new NumericConstant(25))));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof NumericConstant);

        Fraction expected = new Fraction(60);
        Assert.assertEquals(expected, simplifiedValue);
    }

    // Tests the negation of different hiearchies of subtraction operators.

    @Test
    public void testSimplifySubtractionTwoOperands() {
        IExpression expression = new Addition(new NumericConstant(10),
                new NumericConstant(-5));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof NumericConstant);

        Fraction expected = new Fraction(5);
        Assert.assertEquals(expected, simplifiedValue);
    }

    @Test
    public void testSimplifySubtractionThreeOperands() {

        IExpression expression = new Addition(new NumericConstant(10),
                new Addition(new NumericConstant(-15), new NumericConstant(-5)));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof NumericConstant);

        Fraction expected = new Fraction(-10);
        Assert.assertEquals(expected, simplifiedValue);
    }

    @Test
    public void testSimplifySubtractionFourOperands() {

        // 5 - 15 - 15 - 25
        IExpression expression = new Addition(new NumericConstant(5),
                new Addition(new NumericConstant(-15), new Addition(
                        new NumericConstant(-15), new NumericConstant(-25))));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof NumericConstant);

        Fraction expected = new Fraction(-50);
        Assert.assertEquals(expected, simplifiedValue);
    }

    // Tests the negation of different hiearchies of multiplication operators.

    @Test
    public void testSimplifyMultiplicationTwoOperands() {
        IExpression expression = new Multiplication(new NumericConstant(10),
                new NumericConstant(5));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof Multiplication);

        Fraction expected = new Fraction(50);
        Assert.assertEquals(expected, simplifiedValue);
    }

    @Test
    public void testSimplifyMultiplicationThreeOperands() {

        IExpression expression = new Multiplication(new NumericConstant(10),
                new Multiplication(new NumericConstant(15),
                        new NumericConstant(5)));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof Multiplication);

        Fraction expected = new Fraction(750);
        Assert.assertEquals(expected, simplifiedValue);
    }

    @Test
    public void testSimplifyMultiplicationFourOperands() {

        IExpression expression = new Multiplication(new NumericConstant(5),
                new Multiplication(new NumericConstant(15), new Multiplication(
                        new NumericConstant(15), new NumericConstant(25))));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof Multiplication);

        Fraction expected = new Fraction(28125);
        Assert.assertEquals(expected, simplifiedValue);
    }

    // Tests the negation of different hiearchies of division operators.

    @Test
    public void testSimplifyDivisionTwoOperands() {
        IExpression expression = new Division(new NumericConstant(10),
                new NumericConstant(5));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof Division);

        Fraction expected = new Fraction(2);
        Assert.assertEquals(expected, simplifiedValue);
    }

    @Test
    public void testSimplifyDivisionThreeOperands() {

        IExpression expression = new Division(new NumericConstant(10),
                new Division(new NumericConstant(15), new NumericConstant(5)));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof Division);

        Fraction expected = new Fraction(10, 3);
        Assert.assertEquals(expected, simplifiedValue);
    }

    @Test
    public void testSimplifyDivisionFourOperands() {

        IExpression expression = new Division(new NumericConstant(5),
                new Division(new NumericConstant(15), new Division(
                        new NumericConstant(15), new NumericConstant(25))));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof Division);

        Fraction expected = new Fraction(1, 5);
        Assert.assertEquals(expected, simplifiedValue);
    }

    // Tests the negation of some mixed cases of operators.

    @Test
    public void testSimplifyAdditionSubtraction() {

        IExpression expression = new Addition(new NumericConstant(20),
                new Addition(new NumericConstant(15), new NumericConstant(-15)));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof NumericConstant);

        Fraction expected = new Fraction(20);
        Assert.assertEquals(expected, simplifiedValue);
    }

    @Test
    public void testSimplifySubtractionAddition() {

        IExpression expression = new Addition(new NumericConstant(10),
                new Addition(new NumericConstant(-15), new NumericConstant(5)));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof NumericConstant);

        Fraction expected = new Fraction(0);
        Assert.assertEquals(expected, simplifiedValue);
    }

    @Test
    public void testSimplifyMultiplicationDivision() {

        IExpression expression = new Multiplication(new NumericConstant(10),
                new Division(new NumericConstant(15), new NumericConstant(5)));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof Multiplication);

        Fraction expected = new Fraction(30);
        Assert.assertEquals(expected, simplifiedValue);
    }

    @Test
    public void testSimplifyDivisionMultiplication() {

        IExpression expression = new Division(new NumericConstant(10),
                new Multiplication(new NumericConstant(15),
                        new NumericConstant(5)));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof Division);

        Fraction expected = new Fraction(2, 15);
        Assert.assertEquals(expected, simplifiedValue);
    }

    @Test
    public void testSimplifyAdditionSubtractionMultiplicationDivision() {

        // 5 + (15 - (10 * (15/25))
        IExpression expression = new Addition(new NumericConstant(5),
                new Addition(new NumericConstant(15), new Multiplication(
                        new NumericConstant(-10), new Division(
                                new NumericConstant(15),
                                new NumericConstant(25)))));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof Addition);

        Fraction expected = new Fraction(14);
        Assert.assertEquals(expected, simplifiedValue);
    }

    @Test
    public void testSimplifySubtractionAdditionMultiplicationDivision() {

        // 5 - (15 + (10 * (15/25))
        IExpression expression = new Addition(new NumericConstant(5),
                new Addition(new NumericConstant(-15), new Multiplication(
                        new NumericConstant(10), new Division(
                                new NumericConstant(15),
                                new NumericConstant(25)))));

        IExpression simplifiedExpression = ExpressionUtils.simplifyExpression(expression);
        Fraction simplifiedValue = simplifiedExpression.evaluate();

        Assert.assertTrue(simplifiedExpression instanceof Addition);

        Fraction expected = new Fraction(-4);
        Assert.assertEquals(expected, simplifiedValue);
    }


}
