package de.uka.ilkd.keyabs.abs.expression;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.keyabs.abs.ABSNonTerminalProgramElement;
import de.uka.ilkd.keyabs.abs.ABSVisitor;
import de.uka.ilkd.keyabs.abs.IABSPureExpression;

public class ABSFnApp extends ABSNonTerminalProgramElement implements
	IABSPureExpression {

    public ProgramElementName getFnName() {
        return fctName;
    }

    private final ProgramElementName fctName;
    private final IABSPureExpression[] arguments;
    

    public ABSFnApp(ProgramElementName fctName,
	    IABSPureExpression[] arguments) {
	    this.fctName = fctName;
        this.arguments = arguments == null ? new IABSPureExpression[0]
                : arguments;
    }
    @Override
    public int getChildCount() {
        return 1 + arguments.length;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        switch (index) {
        case 0:
            return fctName;
        default:
            return getArgumentAt(index - 1);
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
        v.performActionOnABSFnApp(this);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(fctName).append("(");

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
