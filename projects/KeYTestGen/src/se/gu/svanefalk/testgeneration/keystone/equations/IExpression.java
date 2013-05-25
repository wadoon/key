package se.gu.svanefalk.testgeneration.keystone.equations;

import org.apache.commons.math3.fraction.Fraction;

import se.gu.svanefalk.testgeneration.keystone.equations.expression.ITreeNode;

public interface IExpression extends ITreeNode {

    Fraction evaluate();
}
