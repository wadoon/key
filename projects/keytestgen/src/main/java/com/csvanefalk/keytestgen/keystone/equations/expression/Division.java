package com.csvanefalk.keytestgen.keystone.equations.expression;

import com.csvanefalk.keytestgen.keystone.equations.IExpression;
import org.apache.commons.math3.fraction.Fraction;

public class Division extends AbstractBinaryExpression {

    public Division(final IExpression leftOperand,
                    final IExpression rightOperand) {
        super(leftOperand, rightOperand);
    }

    @Override
    public Fraction evaluate() {
        return getLeftOperand().evaluate().divide(getRightOperand().evaluate());
    }

    @Override
    public String toString() {

        return "(" + getLeftOperand().toString() + "/"
                + getRightOperand().toString() + ")";
    }
}
