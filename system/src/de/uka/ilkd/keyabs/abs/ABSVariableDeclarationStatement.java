package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.op.IProgramVariable;

public class ABSVariableDeclarationStatement extends
        ABSNonTerminalProgramElement implements IABSStatement {

    private final TypeReference type;
    private final IProgramVariable var;
    private final IABSExpression exp;

    public ABSVariableDeclarationStatement(TypeReference type,
            IProgramVariable var, IABSExpression initExp) {
        this.type = type;
        this.var = var;
        this.exp = initExp;
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

    /**
     * equals modulo renaming is described in the corresponding comment in class
     * SourceElement. The variables declared in the local variable declaration
     * have to be added to the NameAbstractionTable.
     */
    @Override
    public boolean equalsModRenaming(SourceElement se, NameAbstractionTable nat) {
        if (!(se instanceof ABSVariableDeclarationStatement)) {
            return false;
        }
        ABSVariableDeclarationStatement vs = (ABSVariableDeclarationStatement) se;
        nat.add(var, vs.var);
        if (vs.getChildCount() != getChildCount()) {
            return false;
        }
        for (int i = 0, cc = getChildCount(); i < cc; i++) {
            if (!getChildAt(i).equalsModRenaming(vs.getChildAt(i), nat)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public int hashCode() {
        int result = 17;
        result = 37 * result + ((type == null) ? 0 : type.hashCode());
        result = 37 * result + getChildCount();
        for (int i = 0, cc = getChildCount(); i < cc; i++) {
            result = 37 * result + getChildAt(i).hashCode();
        }
        return result;
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

    @Override
    public String toString() {
        return type + " " + var + (exp != null ? " = " + exp : "");
    }

}
