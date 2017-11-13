package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class IsPExpression extends VariableConditionAdapter {

    private SchemaVariable checkExpr;
    private SchemaVariable pseqExpr;

    public IsPExpression(SchemaVariable checkExpr, SchemaVariable pseq) {
        this.checkExpr = checkExpr;
        this.pseqExpr = pseq;
    }
    
    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate,
            SVInstantiations instMap, Services services) {    
        Object selfInst;
        Object checkInst;
        
        if (var == this.checkExpr) {            
            checkInst = instCandidate;
            selfInst = instMap.getInstantiation(this.pseqExpr);
        } else if (var == this.pseqExpr){            
            checkInst = instMap.getInstantiation(this.checkExpr);
            selfInst = instCandidate;
        } else {
            //Called with another schema var than the ones needed. Therefore, check if the others are instantiated.
            checkInst = instMap.getInstantiation(this.checkExpr);
            selfInst = instMap.getInstantiation(this.pseqExpr);
            assert(checkInst != null && selfInst != null);
        } 
            
        return checkHelper(checkInst, selfInst, services);
    }
    
    
    private boolean checkHelper(Object check, Object pseq, Services services) {
        if (pseq instanceof Term && check instanceof Term) {
            Term pseqterm = (Term) pseq; 
            if (pseqterm.sort().equals(services.getTypeConverter().getSeqLDT().targetSort())) {
               return checkHelperSeq((Term)check, pseqterm, services);
            } else {
                return false;
            }
        } else {
            return false;
        }
    }
   
    private boolean checkHelperSeq(Term check, Term paramseq, Services services) {
        if (paramseq.op().equals(services.getTypeConverter().getSeqLDT().getSeqConcat())) {
            //parameters are a concatenation. check for all subterms recursively
            return checkHelperSeq(check, paramseq.sub(0), services) || checkHelperSeq(check, paramseq.sub(1), services);
        } else if (paramseq.op().equals(services.getTypeConverter().getSeqLDT().getSeqSingleton())) {
            return checkHelperTerm(check, paramseq.sub(0), services);
        } else {
            return false;
        }
    }
    
    private boolean checkHelperTerm(Term check, Term param, Services services) {
        if (check.equals(param)) {
            //found it
            return true;
        } else if (services.getTypeConverter().getHeapLDT().isSelectOp(check.op())) {
               //check is a select expression. so walk down
                return checkHelper(check.sub(1), param, services);
       } else {
            return false;
       }
    }
    
   
    
    @Override
    public String toString() {
        return "\\isPExpression (" + this.checkExpr + ", " + this.pseqExpr + ")";
    }

}
