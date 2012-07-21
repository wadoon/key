package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;

public class ABSAddExp extends ABSBinaryOperatorPureExp {

    public ABSAddExp(IABSPureExpression left, IABSPureExpression right) {
        super(left, right);
    }

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
        return ((ABSTypeConverter)services.getTypeConverter()).getABSIntType();
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSAddExp(this);
    }

}
