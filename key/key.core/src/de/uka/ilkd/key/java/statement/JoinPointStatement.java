package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.join.JoinProcedure;
import de.uka.ilkd.key.speclang.BlockContract;

public class JoinPointStatement extends JavaStatement{
    
    private BlockContract joinContract;
    private JoinProcedure joinProc;
    private ProgramVariable prgVar;
    
    public JoinPointStatement(BlockContract joinContract) {
       this.joinContract = joinContract;
       this.joinProc = joinContract.getJoinProcedure();
    }  
    
    public JoinPointStatement(BlockContract joinContract,
            ProgramVariable progVar) {
        this.joinContract = joinContract;
        this.joinProc = joinContract.getJoinProcedure(); 
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
        return joinProc;
    }
    public void setJoinProc(JoinProcedure joinProc) {
        this.joinProc = joinProc;
    }
    
    public String toString(){
        return (prgVar.toString());
        
    }

    public BlockContract getContract() {
        return joinContract;
    }

}
