package de.uka.ilkd.keyabs.abs;

import abs.frontend.ast.ASTNode;
import abs.frontend.ast.ExpressionStmt;
import abs.frontend.ast.IncompleteSyncAccess;
import abs.frontend.ast.VarUse;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.IProgramVariable;

public class SchemaABS2KeYABSConverter extends AbstractABS2KeYABSConverter {

    
    private final Namespace schemaVariables;

    public SchemaABS2KeYABSConverter(Namespace schemaVariables) {
        this.schemaVariables = schemaVariables;
    }
    
    @Override
    protected ProgramElement requestConversion(ASTNode<?> x) {
        IProgramVariable result = null;
        if (x instanceof ExpressionStmt) {
            System.out.println(x + ":" + x.getNumChild());
            if (((ExpressionStmt)x).getNumChild() == 2) {
                if (x.getChild(1) instanceof IncompleteSyncAccess) {
                    System.out.println(x.getChild(1).getChild(0));
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

    @Override
    protected IProgramVariable lookupLocalVariable(String name) {
        return lookup(name);
    }

    @Override
    protected IProgramVariable lookupFieldVariable(String name) {
        return lookup(name);
    }

}
