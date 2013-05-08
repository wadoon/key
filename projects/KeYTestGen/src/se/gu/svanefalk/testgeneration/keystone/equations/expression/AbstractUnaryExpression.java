package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public abstract class AbstractUnaryExpression implements IExpression {

    public AbstractUnaryExpression(IExpression operand) {
        super();
        this.operand = operand;
    }

    private IExpression operand = null;

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
    public void setOperand(IExpression operand) {
        this.operand = operand;
    }

}
