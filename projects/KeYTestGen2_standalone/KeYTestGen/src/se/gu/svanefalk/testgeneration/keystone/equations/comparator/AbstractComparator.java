package se.gu.svanefalk.testgeneration.keystone.equations.comparator;

import se.gu.svanefalk.testgeneration.keystone.equations.IComparator;
import se.gu.svanefalk.testgeneration.keystone.equations.IExpression;
import se.gu.svanefalk.testgeneration.keystone.equations.expression.ITreeNode;

public abstract class AbstractComparator implements IComparator, ITreeNode {

    private IExpression leftOperand = null;
    private IExpression rightOperand = null;

    public AbstractComparator(final IExpression leftOperand,
            final IExpression rightOperand) {
        super();
        this.leftOperand = leftOperand;
        this.rightOperand = rightOperand;

        this.leftOperand.setParent(this);
        this.rightOperand.setParent(this);
    }

    /**
     * @return the leftOperand
     */
    public IExpression getLeftOperand() {
        return leftOperand;
    }

    @Override
    public ITreeNode getParent() {
        // TODO Auto-generated method stub
        return null;
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
        this.leftOperand.setParent(this);
    }

    @Override
    public void setParent(final ITreeNode parent) {
        // TODO Auto-generated method stub

    }

    /**
     * @param rightOperand
     *            the rightOperand to set
     */
    public void setRightOperand(final IExpression rightOperand) {
        this.rightOperand = rightOperand;
        this.rightOperand.setParent(this);
    }
}