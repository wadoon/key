package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.IProgramVariable;

public class JoinPointStatement extends JavaStatement {

    private IProgramVariable prgVar;

    public JoinPointStatement(IProgramVariable progVar) {
        this.prgVar = progVar;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnJoinPointStatement(this);
    }

    @Override
    public int getChildCount() {
        return 1;
    }
    
    public IProgramVariable getProgVar() {
        return prgVar;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        return index == 0 ? prgVar : null;
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printJoinPoint(this);
    }


    public String toString() {
        return "join_point(" + prgVar.toString() + ");";

    }
    
    @Override
    public boolean equals(Object o) {
        return (o instanceof JoinPointStatement) &&
                ((JoinPointStatement) o).prgVar.equals(prgVar);
    }

}
