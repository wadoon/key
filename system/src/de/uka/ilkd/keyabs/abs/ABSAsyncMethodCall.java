package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.ProgramElementName;

public class ABSAsyncMethodCall extends ABSNonTerminalProgramElement implements
IABSMethodReference {

    private final IABSPureExpression caller;
    private final ProgramElementName methodName;
    private final IABSPureExpression[] arguments;

    public ABSAsyncMethodCall(IABSPureExpression caller,
            ProgramElementName methodName, IABSPureExpression[] arguments) {
        super();
        this.caller = caller;
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
            return caller;
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

    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(caller).append("!").append(methodName).append("(");

        for (int i = 0; i < arguments.length; i++) {
            sb.append(arguments[i]);
        }

        sb.append(")");
        return sb.toString();
    }
}
