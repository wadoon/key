package de.uka.ilkd.keyabs.abs.expression;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.keyabs.abs.ABSNonTerminalProgramElement;
import de.uka.ilkd.keyabs.abs.ABSVisitor;
import de.uka.ilkd.keyabs.abs.IABSPureExpression;

public class ABSMinusExp extends ABSNonTerminalProgramElement implements
        IABSPureExpression {

    public ABSMinusExp(IABSPureExpression exp) {
        super();
        this.exp = exp;
    }

    private final IABSPureExpression exp;

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
        return exp.getKeYJavaType(services, ec);
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        if (index == 0) {
            return exp;
        }
        throw new IndexOutOfBoundsException();
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSMinusExp(this);
    }

    @Override
    public String toString() {
        return "-1*(" + exp.toString() + ")";
    }

}
