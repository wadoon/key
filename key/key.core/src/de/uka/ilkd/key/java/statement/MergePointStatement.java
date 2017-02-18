package de.uka.ilkd.key.java.statement;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public class MergePointStatement extends JavaStatement {

    private ProgramVariable prgVar;

    public MergePointStatement(ExtList children) {
        super(children);
        this.prgVar = children.get(ProgramVariable.class);
    }

    public MergePointStatement(ProgramVariable progVar) {
        this.prgVar = progVar;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnMergePointStatement(this);
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        return index == 0 ? prgVar : null;
    }

    public ProgramVariable getProgVar() {
        return prgVar;
    }

    public boolean equals(Object o) {
        return (o != null && o instanceof MergePointStatement
                && prgVar.equals(((MergePointStatement) o).prgVar));
    }

    public String toString() {
        return (prgVar.toString());
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printMergePoint(this);
    }

}
