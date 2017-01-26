package de.uka.ilkd.key.java.statement;

import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
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
         this.joinParams = joinParams;
         this.prgVar = progVar;
         this.joinProc = joinProc.toString().equals("JoinByPredicateAbstraction") ? getJoinProcWithParams(joinParams) : joinProc;
        }

    private JoinProcedure getJoinProcWithParams(String joinParams) {
//        Pattern p = Pattern.compile("\\\\(.+?)\\( ([^\\\\]+)\\)");
//        Matcher m = p.matcher(joinParams);
//        boolean matched = false;
//
//        while (m.find()) {
//            matched = true;
//            if (m.groupCount() != 2)
//                return false;
//            else {
//                List<AbstractionPredicate> predicates = getPredicates(
//                        m.group(2), services);
//                if (((m.group(1).equals("conjunctive")
//                        || m.group(1).equals("disjunctive")
//                        || m.group(1).equals("simple")) && predicates.isEmpty())
//                        || !m.group(1).equals("rep"))
//                    return false;
//            }
//        }
        return null;
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
