package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.logic.op.IProgramVariable;


public class ABSLocalVariableReference extends ABSVariableReference
        implements IABSLocationReference {

    public ABSLocalVariableReference(IProgramVariable variable, PositionInfo pos) {
        super(variable, pos);
    }

    public ABSLocalVariableReference(IProgramVariable variable) {
        super(variable, null);
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSLocalVariableReference(this);
    }

    public String toString() {
        return getVariable().name().toString();
    }
    
}
