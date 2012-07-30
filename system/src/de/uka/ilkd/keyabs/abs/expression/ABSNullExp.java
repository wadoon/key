package de.uka.ilkd.keyabs.abs.expression;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.keyabs.abs.ABSProgramElement;
import de.uka.ilkd.keyabs.abs.ABSVisitor;
import de.uka.ilkd.keyabs.abs.IABSPureExpression;

public class ABSNullExp extends ABSProgramElement implements IABSPureExpression {

	@Override
	public void visit(ABSVisitor v) {
		v.performActionOnABSNullExp(this);
	}
	
	public String toString() {
		return "null";
	}

	@Override
	public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
		throw new RuntimeException("TODO");
	}

}
