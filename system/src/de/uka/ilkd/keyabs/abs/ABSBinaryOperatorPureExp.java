package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;

public class ABSBinaryOperatorPureExp extends ABSNonTerminalProgramElement implements IABSPureExpression {

    private final IABSPureExpression left;
    private final IABSPureExpression right;
    
    
    
    public ABSBinaryOperatorPureExp(IABSPureExpression left,
            IABSPureExpression right) {
        super();
        this.left = left;
        this.right = right;
    }



    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
        return services.getTypeConverter().getIntegerLDT();
    }



    @Override
    public int getChildCount() {
        // TODO Auto-generated method stub
        return 0;
    }



    @Override
    public ProgramElement getChildAt(int index) {
        // TODO Auto-generated method stub
        return null;
    }



    @Override
    public void visit(ABSVisitor v) {
        // TODO Auto-generated method stub
        
    }
    
    
    
    
    
    

}
