package de.uka.ilkd.keyabs.abs;



import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.keyabs.abs.ABSNonTerminalProgramElement;
import de.uka.ilkd.keyabs.abs.ABSVisitor;
import de.uka.ilkd.keyabs.abs.IABSPureExpression;

public class ABSDataConstructor extends ABSNonTerminalProgramElement  {

    private final ProgramElementName constructorName;
   private final IABSPureExpression[] args;
    
  //  public ABSDataConstructor(ProgramElementName constructorName, IABSPureExpression[] args) {
    public ABSDataConstructor(ProgramElementName constructorName) {
//	this.args = (args == null ? new IABSPureExpression[0] : args);
	this.constructorName = constructorName;
    this.args = new IABSPureExpression[0];
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
	v.performActionOnABSDataConstructor(this);
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

    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
	return services.getProgramInfo().getKeYJavaType(services.getNamespaces().functions().lookup(constructorName).sort());
    }

}