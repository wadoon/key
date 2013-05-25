package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public class Subtraction extends AbstractBinaryExpression {

    public Subtraction(final IExpression leftOperand,
            final IExpression rightOperand) {
        super(leftOperand, rightOperand);
    }

    @Override
    public Fraction evaluate() {
        return getLeftOperand().evaluate().subtract(
                getRightOperand().evaluate());
    }

    @Override
    public String toString() {

        return "(" + getLeftOperand().toString() + " - "
                + getRightOperand().toString() + ")";
    }
}