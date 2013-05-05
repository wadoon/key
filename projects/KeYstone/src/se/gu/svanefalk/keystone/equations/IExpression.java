package se.gu.svanefalk.keystone.equations;

import javax.naming.OperationNotSupportedException;

import org.apache.commons.math3.fraction.Fraction;

public interface IExpression {

    Fraction evaluate() throws OperationNotSupportedException;
}
