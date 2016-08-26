package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.reference.MethodName;

public class ABSAsyncMethodCall extends ABSMethodCall  {

    public ABSAsyncMethodCall(IABSPureExpression callee,
            MethodName methodName, IABSPureExpression[] arguments) {
    	super(callee, methodName, arguments);
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
}
