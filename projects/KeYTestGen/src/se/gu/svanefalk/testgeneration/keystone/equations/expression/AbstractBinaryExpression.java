package se.gu.svanefalk.testgeneration.keystone.equations.expression;

import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;

public abstract class AbstractBinaryExpression implements IExpression {

    private IExpression leftOperand = null;
    private IExpression rightOperand = null;

    public AbstractBinaryExpression(final IExpression leftOperand,
            final IExpression rightOperand) {
        super();
        this.leftOperand = leftOperand;
        this.rightOperand = rightOperand;
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
     * @param leftOperand
     *            the leftOperand to set
     */
    public void setLeftOperand(final IExpression leftOperand) {
        this.leftOperand = leftOperand;
    }

    /**
     * @param rightOperand
     *            the rightOperand to set
     */
    public void setRightOperand(final IExpression rightOperand) {
        this.rightOperand = rightOperand;
    }
}
