package se.gu.svanefalk.keystone.equations.comparator;

import javax.naming.OperationNotSupportedException;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.keystone.equations.IExpression;

public class LessOrEquals extends AbstractComparator {

    public LessOrEquals(IExpression leftOperand, IExpression rightOperand) {
        super(leftOperand, rightOperand);
    }

    @Override
    public boolean evaluate() throws OperationNotSupportedException {

        Fraction leftOperand = getLeftOperand().evaluate();
        Fraction rightOperand = getRightOperand().evaluate();

        int leftDividend = rightOperand.getDenominator()
                * leftOperand.getNumerator();
        int rightDividend = rightOperand.getNumerator()
                * leftOperand.getDenominator();

        return leftDividend <= rightDividend;
    }
}