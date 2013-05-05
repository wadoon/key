package se.gu.svanefalk.keystone.equations.comparator;

import se.gu.svanefalk.keystone.equations.IComparator;
import se.gu.svanefalk.keystone.equations.IExpression;

public abstract class AbstractComparator implements IComparator {

    private IExpression leftOperand = null;
    private IExpression rightOperand = null;

    public AbstractComparator(IExpression leftOperand, IExpression rightOperand) {
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
     * @param leftOperand
     *            the leftOperand to set
     */
    public void setLeftOperand(IExpression leftOperand) {
        this.leftOperand = leftOperand;
    }

    /**
     * @return the rightOperand
     */
    public IExpression getRightOperand() {
        return rightOperand;
    }

    /**
     * @param rightOperand
     *            the rightOperand to set
     */
    public void setRightOperand(IExpression rightOperand) {
        this.rightOperand = rightOperand;
    }
}