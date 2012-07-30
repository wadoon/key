package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.ProgramElementName;

public class ABSDataConstructorExp extends ABSNonTerminalProgramElement implements IABSPureExpression {

    private final ProgramElementName constructorName;
    private final IABSPureExpression[] args;
    
    public ABSDataConstructorExp(ProgramElementName constructorName, IABSPureExpression[] args) {
	this.args = (args == null ? new IABSPureExpression[0] : args);
	this.constructorName = constructorName;
    }
    
    @Override
    public int getChildCount() {
	return 1 + args.length;
    }

    @Override
    public ProgramElement getChildAt(int index) {
	if (index == 0) {
	    return constructorName;
	}
	return args[index - 1];
    }

    @Override
    public void visit(ABSVisitor v) {
	v.performActionOnABSDataConstructorExp(this);
    }
    
    public String toString() {
	StringBuilder sb = new StringBuilder();
	sb.append(constructorName);
	sb.append("(");
	for (IABSPureExpression exp : args) {
	    sb.append(exp);
	    sb.append(",");
	}
	if (args.length != 0) sb.deleteCharAt(sb.length() - 1);
	sb.append(")");
	return sb.toString();
    }

    public int getArgumentCount() {
	return args.length;
    }

    public IABSPureExpression getArgumentAt (int i) {
	return args[i];
    }

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
	return services.getProgramInfo().getKeYJavaType(services.getNamespaces().functions().lookup(constructorName).sort());
    }

}
