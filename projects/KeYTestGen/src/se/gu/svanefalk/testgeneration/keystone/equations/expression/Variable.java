package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import javax.naming.OperationNotSupportedException;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public class Variable implements IExpression {

    @Override
    public Fraction evaluate() throws OperationNotSupportedException {
        throw new OperationNotSupportedException(
                "Variables are undefined and cannot be evaluated");
    }
}