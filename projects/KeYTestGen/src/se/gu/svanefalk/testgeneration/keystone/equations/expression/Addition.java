package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import javax.naming.OperationNotSupportedException;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public class Addition extends AbstractExpression {

    public Addition(final IExpression leftOperand,
            final IExpression rightOperand) {
        super(leftOperand, rightOperand);
    }

    @Override
    public Fraction evaluate() throws OperationNotSupportedException {
        return getLeftOperand().evaluate().add(getRightOperand().evaluate());
    }

}
