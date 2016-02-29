package de.uka.ilkd.keyabs.abs.expression;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.keyabs.abs.ABSProgramElement;
import de.uka.ilkd.keyabs.abs.ABSVisitor;
import de.uka.ilkd.keyabs.abs.IABSPureExpression;


public class ABSNegExp extends ABSProgramElement implements IABSPureExpression{
	
	public ABSNegExp(IABSPureExpression expression) {
    	this.expression = expression;
    }
	
	private final IABSPureExpression expression;


    @Override
	public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("! ").append(expression).append('\n');

        return sb.toString();
    }

    public IABSPureExpression getExpression() {
        return expression;
    }
    
	@Override
	public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
		return null;
	}
	
	@Override
	public void visit(ABSVisitor v) {
		v.performActionOnABSNegExp(this);
	}
}
