package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.op.IProgramVariable;

public abstract class ABSVariableReference extends ABSNonTerminalProgramElement 
                                           implements IABSPureExpression {

    private final IProgramVariable variable;
    
    
    public ABSVariableReference(IProgramVariable variable, PositionInfo pos) {
        super(pos);
        this.variable = variable;
    }

    public IProgramVariable getVariable() {
        return variable;
    }
    

    @Override
    public KeYJavaType getKeYJavaType(IServices services, ExecutionContext ec) {
        return variable.getKeYJavaType();
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        if (index != 0) throw new IndexOutOfBoundsException();
        return variable;
    }
}