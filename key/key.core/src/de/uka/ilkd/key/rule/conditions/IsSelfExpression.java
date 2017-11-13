package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class IsSelfExpression extends VariableConditionAdapter {

    private SchemaVariable checkExpr;
    private SchemaVariable selfExpr;

    public IsSelfExpression(SchemaVariable checkExpr, SchemaVariable selfExpr) {
        this.checkExpr = checkExpr;
        this.selfExpr = selfExpr;
    }
    
    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate,
            SVInstantiations instMap, Services services) {    
        Object selfInst;
        Object checkInst;
        
        if (var == this.checkExpr) {            
            checkInst = instCandidate;
            selfInst = instMap.getInstantiation(this.selfExpr);
        } else if (var == this.selfExpr){            
            checkInst = instMap.getInstantiation(this.checkExpr);
            selfInst = instCandidate;
        } else {
            //Called with another schema var than the ones needed. Therefore, check if the others are instantiated.
            checkInst = instMap.getInstantiation(this.checkExpr);
            selfInst = instMap.getInstantiation(this.selfExpr);
        } 
        if(checkInst == null || selfInst == null) {
            return false;
        }
        return checkHelper(checkInst, selfInst, services);
    }
   
    private boolean checkHelper(Object check, Object self, Services services) {
        if (check.equals(self)) {
            return true;
        } else if (self instanceof Term && check instanceof Term) {
            //walk down the check expression
            Term checkterm = (Term)check;
            if (services.getTypeConverter().getHeapLDT().isSelectOp(checkterm.op())) {
                return checkHelper(checkterm.sub(1), self, services);
            } else {
                return false;
            }
        } else {
            return false;
        }
    }
    
    @Override
    public String toString() {
        return "\\isSelfExpression (" + this.checkExpr + ", " + this.selfExpr + ")";
    }

}
