package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;

public class ABSAsyncMethodCall extends ABSNonTerminalProgramElement implements
        IABSMethodReference, IABSExpression, IABSStatement {

    private final IABSPureExpression callee;
    private final MethodName methodName;
    private final IABSPureExpression[] arguments;

    public ABSAsyncMethodCall(IABSPureExpression callee,
            MethodName methodName, IABSPureExpression[] arguments) {
        super();
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
    public void visit(ABSVisitor v) {
        v.performActionOnABSAsyncMethodCall(this);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(callee).append("!").append(methodName).append("(");

        for (int i = 0; i < arguments.length; i++) {
            sb.append(arguments[i]);
        }

        sb.append(")");
        return sb.toString();
    }

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
        return null;
    }
}
