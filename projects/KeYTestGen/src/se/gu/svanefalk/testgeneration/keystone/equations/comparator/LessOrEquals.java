package se.gu.svanefalk.testgeneration.keystone.equations.comparator;

import javax.naming.OperationNotSupportedException;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public class LessOrEquals extends AbstractComparator {

    public LessOrEquals(final IExpression leftOperand,
            final IExpression rightOperand) {
        super(leftOperand, rightOperand);
    }

    @Override
    public boolean evaluate() throws OperationNotSupportedException {

        final Fraction leftOperand = getLeftOperand().evaluate();
        final Fraction rightOperand = getRightOperand().evaluate();

        final int leftDividend = rightOperand.getDenominator()
                * leftOperand.getNumerator();
        final int rightDividend = rightOperand.getNumerator()
                * leftOperand.getDenominator();

        return leftDividend <= rightDividend;
    }

    @Override
    public String toString() {

        return getLeftOperand().toString() + " <= "
                + getRightOperand().toString();
    }
}