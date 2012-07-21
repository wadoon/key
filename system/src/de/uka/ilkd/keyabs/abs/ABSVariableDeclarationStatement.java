package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.op.IProgramVariable;

public class ABSVariableDeclarationStatement extends ABSNonTerminalProgramElement
        implements IABSStatement {

    private final TypeReference type;
    private final IProgramVariable var;
    private final IABSExpression exp;

    public ABSVariableDeclarationStatement(TypeReference type,
            IProgramVariable var, IABSExpression initExp) {
        this.type = type;
        this.var  = var;
        this.exp  = initExp;
    }

    @Override
    public int getChildCount() {
        return exp == null ? 2 : 3;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        switch (index) {
        case 0:
            return type;
        case 1:
            return var;
        case 2:
            if (exp != null)
                return exp;
            ;
        default:
            throw new IndexOutOfBoundsException();
        }

    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSVariableDeclarationStatement(this);
    }

    public IProgramVariable getVariable() {
        return var;
    }

    public IABSExpression getInitializer() {
        return exp;
    }

    public ProgramElement getTypeReference() {
        return type;
    }

}
