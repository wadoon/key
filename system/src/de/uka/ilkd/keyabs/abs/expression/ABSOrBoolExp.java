package de.uka.ilkd.keyabs.abs.expression;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.keyabs.abs.ABSTypeConverter;
import de.uka.ilkd.keyabs.abs.ABSVisitor;
import de.uka.ilkd.keyabs.abs.IABSPureExpression;

public class ABSOrBoolExp extends ABSBinaryOperatorPureExp {

    public ABSOrBoolExp(IABSPureExpression left, IABSPureExpression right) {
        super(left, right);
    }

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
        return ((ABSTypeConverter)services.getTypeConverter()).getBooleanType();
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSOrBoolExp(this);
    }

    @Override
	public String toString() {
    	return getChildAt(0) + " || " + getChildAt(1);
    }

    
}
