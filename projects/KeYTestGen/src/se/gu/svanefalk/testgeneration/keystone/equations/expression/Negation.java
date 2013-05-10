package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import javax.naming.OperationNotSupportedException;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public class Negation extends AbstractUnaryExpression {

    private static final Fraction minusOne = new Fraction(-1);

    public Negation(IExpression operand) {
        super(operand);
    }

    @Override
    public Fraction evaluate() throws OperationNotSupportedException {
        return getOperand().evaluate().multiply(minusOne);
    }

    @Override
    public String toString() {
        return "-(" + getOperand() + ")";
    }
}