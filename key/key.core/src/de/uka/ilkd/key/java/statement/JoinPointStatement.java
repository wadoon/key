package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.rule.join.JoinProcedure;

public class JoinPointStatement extends JavaStatement{
    private JoinProcedure joinProc;
    private String statement;
    private int num;
  
    public JoinPointStatement(JoinProcedure joinProc, int num) {
        this.setJoinProc(joinProc);
        this.setNum(num);
        setStatement("JOIN POINT " + num);
    }
    @Override
    public void visit(Visitor v) {
        // TODO Auto-generated method stub
        
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
    public String getStatement() {
        return statement;
    }
    public void setStatement(String statement) {
        this.statement = statement;
    }
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printJoinPoint(num);
    }

    public int getNum() {
        return num;
    }
    public void setNum(int num) {
        this.num = num;
    }
    public JoinProcedure getJoinProc() {
        return joinProc;
    }
    public void setJoinProc(JoinProcedure joinProc) {
        this.joinProc = joinProc;
    }
    
    public String toString(){
        return statement;
        
    }

}
