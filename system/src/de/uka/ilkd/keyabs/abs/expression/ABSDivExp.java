package de.uka.ilkd.keyabs.abs.expression;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.keyabs.abs.ABSTypeConverter;
import de.uka.ilkd.keyabs.abs.ABSVisitor;
import de.uka.ilkd.keyabs.abs.IABSPureExpression;

public class ABSDivExp extends ABSBinaryOperatorPureExp {

    private final boolean isRatType;

	public ABSDivExp(IABSPureExpression left, IABSPureExpression right, boolean isRatType) {
        super(left, right);
        this.isRatType = isRatType;
    }

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
        return ((ABSTypeConverter)services.getTypeConverter()).getABSIntType();
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSDivExp(this);
    }

    @Override
	public String toString() {
    	return getChildAt(0) + " / " + getChildAt(1);
    }

	public boolean isRatType() {
		return isRatType;
	}    
}
