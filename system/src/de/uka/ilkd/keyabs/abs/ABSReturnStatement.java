package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.keyabs.abs.*;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 22.03.13
 * Time: 07:30
 * To change this template use File | Settings | File Templates.
 */
public class ABSReturnStatement extends ABSNonTerminalProgramElement implements IABSStatement {

    private final IABSExpression retExp;

    public ABSReturnStatement(IABSExpression retExp) {
        this.retExp = retExp;
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSReturnStatement(this);
    }

    @Override
    public int getChildCount() {
        return retExp == null ? 0 : 1;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        if (getChildCount() == 0) throw new IllegalArgumentException();
        return retExp;
    }
}
