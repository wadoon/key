package de.uka.ilkd.keyabs.abs;

import abs.frontend.ast.ASTNode;
import abs.frontend.ast.AsyncCall;
import abs.frontend.ast.ExpressionStmt;
import abs.frontend.ast.IncompleteSyncAccess;
import abs.frontend.ast.PureExp;
import abs.frontend.ast.VarDeclStmt;
import abs.frontend.ast.VarUse;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.keyabs.logic.sort.ABSProgramSVSort;

public class SchemaABS2KeYABSConverter extends AbstractABS2KeYABSConverter {

    private final Namespace<IProgramVariable> schemaVariables;

    public SchemaABS2KeYABSConverter(
            Namespace<IProgramVariable> schemaVariables, IServices services) {
        super(services);
        this.schemaVariables = schemaVariables;
    }

    @Override
    protected ProgramElement requestConversion(ASTNode<?> x) {
        IProgramVariable result = null;
        if (x instanceof ExpressionStmt) {
            if (x.getNumChild() == 2) {
                if (x.getChild(1) instanceof IncompleteSyncAccess) {
                    final String name = ((VarUse) x
                            .getChild(1).getChild(0)).getName();
                    result = lookup(name);
                }
            }
        }
        return result;
    }

    public ABSAsyncMethodCall convert(AsyncCall x) {
        IABSPureExpression callee = (IABSPureExpression) convert(x.getCallee());
        
        
        IProgramVariable methodNameSV = lookup(x.getMethod());
        
        MethodName methodName = (MethodName) (methodNameSV != null ? methodNameSV :
                new ProgramElementName(x.getMethod()));

        IABSPureExpression[] arguments = new IABSPureExpression[x.getNumParam()];

        int i = 0;
        for (PureExp arg : x.getParamList()) {
            arguments[i] = (IABSPureExpression) convert(arg);
            i++;
        }

        return new ABSAsyncMethodCall(callee, methodName, arguments);
    }

    
    IProgramVariable lookup(String name) {
        return schemaVariables.lookup(new Name(name));
    }

    @Override
    public Expression convert(VarUse varUse) {
        IProgramVariable var = lookupLocalVariable(varUse.getName());

        if (var instanceof SchemaVariable) {
            if (var.sort() == ABSProgramSVSort.ABS_PUREEXPRESSION) {
                return (ProgramSV) var;
            } else if (var.sort() == ABSProgramSVSort.ABS_FIELD) {
                return new ABSFieldReference(var);
            }
        }
        return new ABSLocalVariableReference(var);
    }

    @Override
    public ABSVariableDeclarationStatement convert(VarDeclStmt x) {
        String typeName;

        typeName = x.getVarDecl().getAccess().toString();

        KeYJavaType type = lookupType(typeName);

        TypeReference typeRef;
        if (type == null) {
            typeRef = (TypeReference) lookup(typeName);
        } else {
            typeRef = new ABSTypeReference(type);
        }

        IProgramVariable localVar = lookup(x.getVarDecl().getName());
        IABSExpression initExp = 
                x.getVarDecl().hasInitExp() ? (IABSExpression) convert(x.getVarDecl().getInitExp()) : null;
        return new ABSVariableDeclarationStatement(typeRef, localVar, initExp);
    }

    @Override
    protected IProgramVariable lookupLocalVariable(String name) {
        return lookup(name);
    }

    @Override
    protected IProgramVariable lookupFieldVariable(String className, String name) {
        return lookup(name);
    }
}
