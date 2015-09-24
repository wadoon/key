package de.uka.ilkd.keyabs.abs.expression;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.keyabs.abs.ABSNonTerminalProgramElement;
import de.uka.ilkd.keyabs.abs.ABSVisitor;
import de.uka.ilkd.keyabs.abs.IABSExpression;
import de.uka.ilkd.keyabs.abs.IABSPureExpression;

public class ABSNewExpression extends ABSNonTerminalProgramElement implements IABSExpression {

    private final ProgramElementName className;
    private final KeYJavaType type;
    private final IABSPureExpression[] args;
    
    public ABSNewExpression(ProgramElementName className, KeYJavaType type, IABSPureExpression[] args) {
	this.args = (args == null ? new IABSPureExpression[0] : args);
	this.className = className;
	this.type = type;
    }
    
    
    @Override
    public int getChildCount() {
	return 1 + args.length;
    }

    @Override
    public ProgramElement getChildAt(int index) {
	if (index == 0) {
	    return className;
	}
	return args[index - 1];
    }

    @Override
    public void visit(ABSVisitor v) {
	v.performActionOnABSNewExp(this);
    }
    
    public String toString() {
	StringBuilder sb = new StringBuilder();
	sb.append(className);
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
	return type;
    }


}
