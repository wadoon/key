package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.rule.join.JoinProcedure;
import de.uka.ilkd.key.rule.join.procedures.JoinIfThenElse;
import de.uka.ilkd.key.speclang.BlockContract;

public class JoinPointStatement extends JavaStatement {

    private JoinProcedure joinProc;
    private IProgramVariable prgVar;
    private String[] joinParams;

    public JoinPointStatement(BlockContract joinContract) {
        this.joinProc = joinContract.getJoinProcedure();
        this.joinParams = joinContract.getJoinParams();
    }

    public JoinPointStatement(BlockContract joinContract,
            IProgramVariable progVar) {
        this.joinProc = joinContract.getJoinProcedure();
        this.joinParams = joinContract.getJoinParams();
        this.prgVar = progVar;
    }

    public JoinPointStatement(IProgramVariable progVar, JoinProcedure joinProc,
            String[] joinParams) {
        this.joinProc = joinProc;
        this.joinParams = joinParams;
        this.prgVar = progVar;
    }

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

    @Override
    public ProgramElement getChildAt(int index) {
        return index == 0 ? prgVar : null;
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {

        p.printJoinPoint(prgVar);
    }

    public JoinProcedure getJoinProc() {
        if (joinProc == null) {
            System.out.println("JoinProcedure: Returning default IfThenElse");
            return JoinIfThenElse.instance();
        }
        
        return joinProc;
    }

    public void setJoinProc(JoinProcedure joinProc) {
        this.joinProc = joinProc;
    }

    public String toString() {
        return "join_point(" + prgVar.toString() + ")";

    }

    public String[] getJoinParams() {
        return joinParams;
    }
    
    @Override
    public boolean equals(Object o) {
        return (o instanceof JoinPointStatement) &&
                ((JoinPointStatement) o).prgVar.equals(prgVar);
    }

}
