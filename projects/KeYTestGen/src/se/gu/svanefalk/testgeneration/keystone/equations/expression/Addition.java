package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import javax.naming.OperationNotSupportedException;

import org.apache.commons.math3.fraction.Fraction;

import de.uka.ilkd.key.strategy.feature.LeftmostNegAtomFeature;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public class Addition extends AbstractBinaryExpression {

    public Addition(final IExpression leftOperand,
            final IExpression rightOperand) {
        super(leftOperand, rightOperand);
    }

    @Override
    public Fraction evaluate() throws OperationNotSupportedException {
        return getLeftOperand().evaluate().add(getRightOperand().evaluate());
    }

    @Override
    public String toString() {
        
        return "(" + getLeftOperand().toString() + " + " + getRightOperand().toString() + ")";
    }
}
