package de.uka.ilkd.keyabs.abs.expression;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.keyabs.abs.ABSVisitor;
import de.uka.ilkd.keyabs.abs.IABSPureExpression;

public class ABSLEQExp extends ABSBinaryOperatorPureExp {

    public ABSLEQExp(IABSPureExpression left, IABSPureExpression right) {
        super(left, right);
    }

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
        return services.getTypeConverter().getBooleanType();
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSLEQExp(this);
    }

    @Override
	public String toString() {
        return getLeft() + " <= " + getRight();
    }
}
