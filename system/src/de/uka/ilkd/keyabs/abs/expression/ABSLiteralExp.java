package de.uka.ilkd.keyabs.abs.expression;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.keyabs.abs.ABSProgramElement;
import de.uka.ilkd.keyabs.abs.IABSPureExpression;

public abstract class ABSLiteralExp extends ABSProgramElement implements IABSPureExpression {

	public ABSLiteralExp() {
		super();
	}

	public ABSLiteralExp(ExtList list) {
		super(list);
	}

	public ABSLiteralExp(PositionInfo pos) {
		super(pos);
	}

	public ABSLiteralExp(ExtList children, PositionInfo pos) {
		super(children, pos);
	}

	@Override
	public abstract KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec);

}