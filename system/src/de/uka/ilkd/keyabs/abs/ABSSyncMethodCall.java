package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.reference.MethodName;

public class ABSSyncMethodCall extends ABSMethodCall {

    public ABSSyncMethodCall(IABSPureExpression callee,
            MethodName methodName, IABSPureExpression[] arguments) {
    	super(callee, methodName, arguments);
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSSyncMethodCall(this);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(callee).append(".").append(methodName).append("(");

        for (int i = 0; i < arguments.length; i++) {
            sb.append(arguments[i]);
        }

        sb.append(")");
        return sb.toString();
    }
}
