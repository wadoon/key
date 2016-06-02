package de.uka.ilkd.key.logic.op;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.DLAbstractOperator;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Term;

public abstract class AbstractOperator extends DLAbstractOperator implements Operator {

    protected AbstractOperator(Name name, 
            int arity, 
            ImmutableArray<Boolean> whereToBind,
            boolean isRigid) {
        super(name, arity, whereToBind, isRigid);
    }


    protected AbstractOperator(Name name, 
            int arity, 
            Boolean[] whereToBind,
            boolean isRigid) {
        super(name, arity, new ImmutableArray<Boolean>(whereToBind), isRigid);
    }        


    protected AbstractOperator(Name name, int arity, boolean isRigid) {
        super(name, arity, (ImmutableArray<Boolean>) null, isRigid);
    }
    /**
     * Allows subclasses to impose custom demands on what constitutes a 
     * valid term using the operator represented by the subclass. 
     */
    protected abstract boolean additionalValidTopLevel(Term term);
    
    
    @Override
    public boolean validTopLevel(Term term) {
    if(arity() != term.arity()
       || arity() != term.subs().size()
       || (whereToBind() == null) != term.boundVars().isEmpty()) {
        return false;
    }
    
    for(int i = 0, n = arity(); i < n; i++) {
        if(term.sub(i) == null) {
        return false;
        }
    }
    
    return additionalValidTopLevel(term);
    }
}
