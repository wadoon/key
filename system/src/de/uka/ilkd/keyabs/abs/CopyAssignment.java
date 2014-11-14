package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ExpressionContainer;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;

public class CopyAssignment extends ABSNonTerminalProgramElement implements
        IABSStatement, ExpressionContainer {

    public CopyAssignment(IABSLocationReference lhs, IABSExpression rhs,
            PositionInfo pos) {
        super(pos);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    public CopyAssignment(IABSLocationReference lhs, IABSExpression rhs) {
        this(lhs, rhs, null);
    }

    private final IABSLocationReference lhs;
    private final IABSExpression rhs;

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        switch (index) {
        case 0:
            return lhs;
        case 1:
            return rhs;
        default:
            throw new IndexOutOfBoundsException();
        }
    }

    @Override
    public int getExpressionCount() {
        return 2;
    }

    @Override
    public Expression getExpressionAt(int index) {
        switch (index) {
        case 0:
            return lhs;
        case 1:
            return rhs;
        default:
            throw new IndexOutOfBoundsException();
        }
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnCopyAssignment(this);
    }

    @Override
    public String toString() {
        return lhs + " = " + rhs + "; \n";
    }

}
