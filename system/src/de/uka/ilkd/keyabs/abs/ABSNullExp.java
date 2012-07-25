package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;

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
