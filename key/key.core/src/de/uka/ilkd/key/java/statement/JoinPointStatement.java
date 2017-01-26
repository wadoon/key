package de.uka.ilkd.key.java.statement;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.join.JoinProcedure;

public class JoinPointStatement extends JavaStatement{
    
    private String joinParams;
    private JoinProcedure joinProc;
    private ProgramVariable prgVar;
  
    public JoinPointStatement(ExtList children) {
        super(children);
        this.joinParams = children.get(String.class);
        this.joinProc = children.get(JoinProcedure.class);
        this.prgVar = children.get(ProgramVariable.class);
        
    }
    public JoinPointStatement(
            ProgramVariable progVar, JoinProcedure joinProc, String joinParams) {
        this.joinProc = joinProc;
        this.joinParams = joinParams;
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
    
    public void setJoinProc(JoinProcedure joinProc) {
        this.joinProc = joinProc;
    }

    public JoinProcedure getJoinProc() {
        return joinProc;
    }
    
    public String getJoinParams() {
        return joinParams;
    }

    public ProgramVariable getProgVar() {
        return prgVar;
    }
    
    public boolean equals(Object o){
       if( o == null || !(o instanceof JoinPointStatement)) return false;
       JoinPointStatement jPS = (JoinPointStatement) o; 
       return prgVar.equals(jPS.prgVar);
       }
    
    public String toString(){
        return (prgVar.toString());
    }
    
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printJoinPoint(this);
    }


}
