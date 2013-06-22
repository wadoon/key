package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

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