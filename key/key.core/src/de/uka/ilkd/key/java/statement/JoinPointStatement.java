package de.uka.ilkd.key.java.statement;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.join.JoinProcedure;

public class JoinPointStatement extends JavaStatement{
    private JoinProcedure joinProc;
    private ProgramVariable prgVar;
  
    public JoinPointStatement(ExtList children) {
        super(children);
        this.prgVar = children.get(ProgramVariable.class);
        this.joinProc = children.get(JoinProcedure.class);
    }
    
    public JoinPointStatement(JoinProcedure joinProc) {
       this.joinProc = joinProc;
    }  
    
    public JoinPointStatement(JoinProcedure joinProcedure,
            ProgramVariable progVar) {
        this.joinProc = joinProcedure;
        this.prgVar = progVar;
        }

    @Override
    public void visit(Visitor v) {
     //v.performActionOnJoinPointStatement(this);
    }
    @Override
    public int getChildCount() {
        // TODO Auto-generated method stub
        return 0;
    }
    @Override
    public ProgramElement getChildAt(int index) {
        // TODO Auto-generated method stub
        return null;
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

}
