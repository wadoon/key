package de.uka.ilkd.keyabs.abs.expression;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.keyabs.abs.ABSVisitor;
import de.uka.ilkd.keyabs.abs.IABSPureExpression;

public class ABSLTExp extends ABSBinaryOperatorPureExp {

    public ABSLTExp(IABSPureExpression left, IABSPureExpression right) {
        super(left, right);
    }

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
        return services.getTypeConverter().getBooleanType();
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSLTExp(this);
    }

    @Override
	public String toString() {
        return getLeft() + " < " + getRight();
    }

}
