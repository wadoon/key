package se.gu.svanefalk.testgeneration.keystone.equations.comparator;

import javax.naming.OperationNotSupportedException;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public class Equals extends AbstractComparator {

    public Equals(final IExpression leftOperand, final IExpression rightOperand) {
        super(leftOperand, rightOperand);
    }

    @Override
    public boolean evaluate() throws OperationNotSupportedException {
        return getLeftOperand().evaluate().equals(getRightOperand().evaluate());
    }
}