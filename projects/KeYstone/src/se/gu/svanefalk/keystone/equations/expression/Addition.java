package se.gu.svanefalk.keystone.equations.expression;

import javax.naming.OperationNotSupportedException;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.AbstractExpression;

public class Addition extends AbstractExpression {

    public Addition(IExpression leftOperand, IExpression rightOperand) {
        super(leftOperand, rightOperand);
    }

    @Override
    public Fraction evaluate() throws OperationNotSupportedException {
        return getLeftOperand().evaluate().add(getRightOperand().evaluate());
    }

}
