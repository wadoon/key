package de.uka.ilkd.key.logic.op;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Operator;
import org.key_project.common.core.logic.op.DLAbstractOperator;
import org.key_project.util.collection.ImmutableArray;

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
 
}
