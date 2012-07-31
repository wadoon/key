package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.logic.op.IProgramVariable;

public class ABSFieldReference extends ABSVariableReference implements
        IABSFieldReference {

    public ABSFieldReference(IProgramVariable field) {
        super(field, null);
    }

    public ABSFieldReference(IProgramVariable field, PositionInfo pos) {
        super(field, pos);
    }

    @Override
    public IProgramVariable getField() {
        return getVariable();
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSFieldReference(this);
    }

    @Override
    public String toString() {
        return "this." + getField().name();
    }
}
