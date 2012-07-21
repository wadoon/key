package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;

public class ThisExpression extends ABSProgramElement
                            implements IABSPureExpression {

    
    
    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
        return ec.getTypeReference().getKeYJavaType();
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnThisExpression(this);
    }

}
