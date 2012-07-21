package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;

public class ABSAndBoolExp extends ABSBinaryOperatorPureExp {

    public ABSAndBoolExp(IABSPureExpression left, IABSPureExpression right) {
        super(left, right);
    }

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
        return ((ABSTypeConverter)services.getTypeConverter()).getBooleanType();
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSAndBoolExp(this);
    }

}