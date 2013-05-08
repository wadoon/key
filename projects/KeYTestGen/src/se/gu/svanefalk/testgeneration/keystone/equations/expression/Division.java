package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import javax.naming.OperationNotSupportedException;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public class Division extends AbstractBinaryExpression {

    public Division(final IExpression leftOperand,
            final IExpression rightOperand) {
        super(leftOperand, rightOperand);
    }

    @Override
    public Fraction evaluate() throws OperationNotSupportedException {
        return getLeftOperand().evaluate().divide(getRightOperand().evaluate());
    }
    

    @Override
    public String toString() {
        
        return getLeftOperand().toString() + "/" + getRightOperand().toString();
    }
}
