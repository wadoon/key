package se.gu.svanefalk.keystone.equations.expression;

import javax.naming.OperationNotSupportedException;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.keystone.equations.IExpression;

public class Division extends AbstractExpression {

    public Division(IExpression leftOperand, IExpression rightOperand) {
        super(leftOperand, rightOperand);
    }

    @Override
    public Fraction evaluate() throws OperationNotSupportedException {
        return getLeftOperand().evaluate().divide(getRightOperand().evaluate());
    }
}
