package com.csvanefalk.keytestgen.keystone.equations.expression;

import com.csvanefalk.keytestgen.keystone.equations.IExpression;

public abstract class AbstractExpression implements IExpression {

    private ITreeNode parent;

    @Override
    public ITreeNode getParent() {
        return parent;
    }

    @Override
    public void setParent(final ITreeNode parent) {
        this.parent = parent;
    }
}