package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public abstract class AbstractUnaryExpression extends AbstractExpression {

    private IExpression operand = null;

    public AbstractUnaryExpression(final IExpression operand) {
        this.operand = operand;
        operand.setParent(this);
    }

    /**
     * @return the operand
     */
    public IExpression getOperand() {
        return operand;
    }

    /**
     * @param operand
     *            the operand to set
     */
    public void setOperand(final IExpression operand) {
        this.operand = operand;
    }

}
