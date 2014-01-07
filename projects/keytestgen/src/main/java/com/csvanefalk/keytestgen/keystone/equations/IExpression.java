package com.csvanefalk.keytestgen.keystone.equations;

import com.csvanefalk.keytestgen.keystone.equations.expression.ITreeNode;
import org.apache.commons.math3.fraction.Fraction;

public interface IExpression extends ITreeNode {

    Fraction evaluate();
}
