package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.ProgramVisitor;
import de.uka.ilkd.key.rule.MatchConditions;

import java.io.IOException;

public class ABSGetExp extends ABSNonTerminalProgramElement implements IABSExpression {

    private final IABSPureExpression callee;

    public ABSGetExp(IABSPureExpression callee) {
        this.callee = callee;
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSGetExp(this);
    }

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
        return null;
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        return callee;
    }
}
