package de.uka.ilkd.keyabs.abs;

import abs.frontend.ast.ASTNode;
import abs.frontend.ast.AssignStmt;
import abs.frontend.ast.Block;
import abs.frontend.ast.FieldUse;
import abs.frontend.ast.VarUse;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.op.IProgramVariable;

public abstract class AbstractABS2KeYABSConverter {

    public ProgramElement convert(ASTNode<?> x) {
        ProgramElement result = null;
        
        if (x instanceof Block) {
            result = convert((Block)x);
        } else if (x instanceof AssignStmt) {
            result = convert((AssignStmt)x);
        } else if (x instanceof FieldUse) {
            result = convert((FieldUse)x);
        } else if (x instanceof VarUse) {
            result = convert((VarUse)x);
        } else {
            throw new IllegalStateException("Unknown AST element " + x + " : " + x.getClass());
        }
        
        return result;
    }

    public ABSStatementBlock convert(Block x) {
        IABSStatement[] bodyStmnts = new IABSStatement[x.getNumStmt()];
        for (int i = 0; i<x.getNumStmt(); i++) {
            bodyStmnts[i] = (IABSStatement) convert(x.getStmt(i));
        }
        
        return new ABSStatementBlock(bodyStmnts);
    }

    public CopyAssignment convert(AssignStmt x) {
        IABSLocationReference lhs = (IABSLocationReference) convert(x.getVar());
        IABSPureExpression rhs = (IABSPureExpression) convert(x.getValue());
        
        return new CopyAssignment(lhs, rhs);
    }

    public ABSFieldReference convert(FieldUse fieldUse) {
        IProgramVariable var = lookupFieldVariable(fieldUse.getName());
        return new ABSFieldReference(var);
    }

    public ABSLocalVariableReference convert(VarUse varUse) {
        IProgramVariable var = lookupLocalVariable(varUse.getName());
        return new ABSLocalVariableReference(var);
    }

    protected abstract IProgramVariable lookupLocalVariable(String name);

    protected abstract IProgramVariable lookupFieldVariable(String name);

}