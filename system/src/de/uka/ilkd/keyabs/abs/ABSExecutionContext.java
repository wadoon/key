package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.ProgramElement;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 06.04.13
 * Time: 22:01
 * To change this template use File | Settings | File Templates.
 */
public class ABSExecutionContext extends ABSNonTerminalProgramElement {

    private final IABSMethodLabel label;
    private final IABSPureExpression result;
    private final IABSPureExpression future;

    public ABSExecutionContext(IABSMethodLabel label,
                               IABSPureExpression result,
                               IABSPureExpression future) {
        this.label = label;
        this.result = result;
        this.future = future;
    }


    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSExecutionContext(this);
    }

    @Override
    public int getChildCount() {
        return 3;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        switch (index) {
            case 0: return label;
            case 1: return result;
            case 2: return future;
            default:
                throw new IndexOutOfBoundsException();
        }
    }

    public IABSMethodLabel getMethodLabel() {
        return label;
    }

    public IABSPureExpression getResult() {
        return result;
    }

    public IABSPureExpression getFuture() {
        return future;
    }
}
