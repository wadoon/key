package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.util.ExtList;

public abstract class ABSMethodCall extends ABSNonTerminalProgramElement implements
	IABSMethodReference, IABSExpression, IABSStatement {

	protected final IABSPureExpression callee;
	protected final MethodName methodName;
	protected final IABSPureExpression[] arguments;

	public ABSMethodCall(IABSPureExpression callee,
            MethodName methodName, IABSPureExpression[] arguments) {
        this.callee = callee;
        this.methodName = methodName;
        this.arguments = arguments == null ? new IABSPureExpression[0]
                : arguments;
	}

	@Override
	public int getChildCount() {
	    return 2 + arguments.length;
	}

	@Override
	public ProgramElement getChildAt(int index) {
	    switch (index) {
	    case 0:
	        return callee;
	    case 1:
	        return methodName;
	    default:
	        return getArgumentAt(index - 2);
	    }
	}

	public IABSPureExpression getArgumentAt(int i) {
	    return arguments[i];
	}

	public int getArgumentCount() {
	    return arguments.length;
	}

	@Override
	public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
	    return null;
	}

}