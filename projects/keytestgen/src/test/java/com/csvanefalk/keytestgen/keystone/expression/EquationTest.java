package com.csvanefalk.keytestgen.keystone.expression;

import com.csvanefalk.keytestgen.keystone.KeYStoneException;
import com.csvanefalk.keytestgen.keystone.equations.Equation;
import com.csvanefalk.keytestgen.keystone.equations.IComparator;
import com.csvanefalk.keytestgen.keystone.equations.IExpression;
import com.csvanefalk.keytestgen.keystone.equations.comparator.Equals;
import com.csvanefalk.keytestgen.keystone.equations.expression.Addition;
import com.csvanefalk.keytestgen.keystone.equations.expression.Multiplication;
import com.csvanefalk.keytestgen.keystone.equations.expression.NumericConstant;
import com.csvanefalk.keytestgen.keystone.equations.expression.Variable;
import org.apache.commons.math3.fraction.Fraction;
import org.junit.Test;

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
