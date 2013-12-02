package com.csvanefalk.keytestgen.keystone.equations.expression;

import com.csvanefalk.keytestgen.keystone.equations.IExpression;

public abstract class AbstractBinaryExpression extends AbstractExpression {

    private IExpression leftOperand = null;
    private IExpression rightOperand = null;

    public AbstractBinaryExpression(final IExpression leftOperand,
                                    final IExpression rightOperand) {

        assert (leftOperand != null);
        assert (rightOperand != null);

        this.leftOperand = leftOperand;
        this.rightOperand = rightOperand;

        leftOperand.setParent(this);
        rightOperand.setParent(this);
    }

    /**
     * @return the leftOperand
     */
    public IExpression getLeftOperand() {
        return leftOperand;
    }

    /**
     * @return the rightOperand
     */
    public IExpression getRightOperand() {
        return rightOperand;
    }

    /**
     * @param leftOperand the leftOperand to set
     */
    public void setLeftOperand(final IExpression leftOperand) {
        this.leftOperand = leftOperand;
        this.leftOperand.setParent(this);
    }

    /**
     * @param rightOperand the rightOperand to set
     */
    public void setRightOperand(final IExpression rightOperand) {
        this.rightOperand = rightOperand;
        this.rightOperand.setParent(this);
    }
}
