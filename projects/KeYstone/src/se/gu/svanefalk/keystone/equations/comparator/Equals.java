package se.gu.svanefalk.keystone.equations.comparator;

import javax.naming.OperationNotSupportedException;

import se.gu.svanefalk.keystone.equations.IExpression;

public class Equals extends AbstractComparator {

    public Equals(IExpression leftOperand, IExpression rightOperand) {
        super(leftOperand, rightOperand);
    }

    @Override
    public boolean evaluate() throws OperationNotSupportedException {
        return getLeftOperand().evaluate().equals(getRightOperand().evaluate());
    }
}