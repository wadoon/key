package se.gu.svanefalk.testgeneration.keystone.expression;

import org.apache.commons.math3.fraction.Fraction;
import org.junit.Test;

import se.gu.svanefalk.testgeneration.keystone.KeYStoneException;
import se.gu.svanefalk.testgeneration.keystone.equations.Equation;
import se.gu.svanefalk.testgeneration.keystone.equations.IComparator;
import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;
import se.gu.svanefalk.testgeneration.keystone.equations.comparator.Equals;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Addition;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Multiplication;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.NumericConstant;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.Variable;

public class EquationTest {

    @Test
    public void TestEquationCreation() throws KeYStoneException {
        IExpression leftHand = new Multiplication(new NumericConstant(
                new Fraction(2)), new Variable("a"));
        IExpression rightHand = new Addition(new NumericConstant(new Fraction(
                10)), new Variable("b"));
        IComparator equals = new Equals(leftHand, rightHand);

        Equation equation = Equation.createEquation(equals);
        System.out.println(equation);
    }
}
