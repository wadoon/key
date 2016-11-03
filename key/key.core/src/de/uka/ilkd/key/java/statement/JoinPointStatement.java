package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.rule.BlockContractBuiltInRuleApp;

public class JoinPointStatement extends JavaStatement{
    private BlockContractBuiltInRuleApp application;
    private String statement;
    private int num;
    public JoinPointStatement() {
        setStatement("JOIN_POINT");
    }
    public JoinPointStatement(final BlockContractBuiltInRuleApp application, int num) {
        this.setApplication(application);
        this.setNum(num);
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
        p.printJoinPoint();
    }
    public BlockContractBuiltInRuleApp getApplication() {
        return application;
    }
    public void setApplication(BlockContractBuiltInRuleApp application) {
        this.application = application;
    }
    public int getNum() {
        return num;
    }
    public void setNum(int num) {
        this.num = num;
    }
    

}
