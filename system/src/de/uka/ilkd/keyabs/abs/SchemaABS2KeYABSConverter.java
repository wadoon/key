package de.uka.ilkd.keyabs.abs;

import abs.frontend.ast.ASTNode;
import abs.frontend.ast.ExpressionStmt;
import abs.frontend.ast.IncompleteSyncAccess;
import abs.frontend.ast.VarUse;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.keyabs.logic.sort.ABSProgramSVSort;

public class SchemaABS2KeYABSConverter extends AbstractABS2KeYABSConverter {

    
    private final Namespace schemaVariables;

    public SchemaABS2KeYABSConverter(Namespace schemaVariables) {
        this.schemaVariables = schemaVariables;
    }
    
    @Override
    protected ProgramElement requestConversion(ASTNode<?> x) {
        IProgramVariable result = null;
        if (x instanceof ExpressionStmt) {
            if (((ExpressionStmt)x).getNumChild() == 2) {
                if (x.getChild(1) instanceof IncompleteSyncAccess) {
                    final String name =((VarUse)((IncompleteSyncAccess)x.getChild(1)).getChild(0)).getName();
                    result = lookup(name);
                }
            }
        }
        return result;
    }
    
    IProgramVariable lookup(String name) {
        return (IProgramVariable) schemaVariables.lookup(new Name(name));
    }

    public Expression convert(VarUse varUse) {
        IProgramVariable var = lookupLocalVariable(varUse.getName());
        
        if (var instanceof SchemaVariable) {
            if (var.sort() == ABSProgramSVSort.ABS_PUREEXPRESSION) {
                return (ProgramSV) var;
            }
        }        
        return new ABSLocalVariableReference(var);
    }

    
    @Override
    protected IProgramVariable lookupLocalVariable(String name) {
        return lookup(name);
    }

    @Override
    protected IProgramVariable lookupFieldVariable(String name) {
        return lookup(name);
    }

}
