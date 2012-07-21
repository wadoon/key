package de.uka.ilkd.keyabs.abs;

import abs.frontend.ast.ASTNode;
import abs.frontend.ast.AddExp;
import abs.frontend.ast.AndBoolExp;
import abs.frontend.ast.AssignStmt;
import abs.frontend.ast.Binary;
import abs.frontend.ast.Block;
import abs.frontend.ast.FieldUse;
import abs.frontend.ast.MultExp;
import abs.frontend.ast.OrBoolExp;
import abs.frontend.ast.VarDeclStmt;
import abs.frontend.ast.VarUse;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;

public abstract class AbstractABS2KeYABSConverter {

    private final IServices services;

    public AbstractABS2KeYABSConverter(IServices services) {
        this.services = services;
    }

    public ProgramElement convert(ASTNode<?> x) {
        ProgramElement result = null;

        if (x instanceof Block) {
            result = convert((Block) x);
        } else if (x instanceof AssignStmt) {
            result = convert((AssignStmt) x);
        } else if (x instanceof FieldUse) {
            result = convert((FieldUse) x);
        } else if (x instanceof VarUse) {
            result = convert((VarUse) x);
        } else if (x instanceof Binary) {
            result = convert((Binary)x);
        } else if (x instanceof VarDeclStmt) {
            result = convert((VarDeclStmt)x);
        }

        if (result == null) {
            result = requestConversion(x);
            if (result == null)
                throw new IllegalStateException("Unknown AST element " + x
                        + " : " + x.getClass());
        }

        return result;
    }

    protected ProgramElement convert(Binary x) {
        ProgramElement result = null;
        if (x instanceof AddExp) {
            result = convert((AddExp) x);
        } else if (x instanceof MultExp) {
            result = convert((MultExp) x);
        } else if (x instanceof AndBoolExp) {
            result = convert((AndBoolExp) x);
        } else if (x instanceof OrBoolExp) {
            result = convert((OrBoolExp) x);
        }
        return result;
    }

    protected ProgramElement requestConversion(ASTNode<?> x) {
        return null;
    }

    protected ProgramElement convert(SchemaVariable value) {
        return (ProgramSV) value;
    }

    public ABSStatementBlock convert(Block x) {
        IABSStatement[] bodyStmnts = new IABSStatement[x.getNumStmt()];
        for (int i = 0; i < x.getNumStmt(); i++) {
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

    public Expression convert(VarUse varUse) {
        IProgramVariable var = lookupLocalVariable(varUse.getName());
        return new ABSLocalVariableReference(var);
    }

    public ABSAddExp convert(AddExp x) {
        return new ABSAddExp((IABSPureExpression) convert(x.getChild(0)),
                (IABSPureExpression) convert(x.getChild(1)));
    }

    public ABSMultExp convert(MultExp x) {
        return new ABSMultExp((IABSPureExpression) convert(x.getChild(0)),
                (IABSPureExpression) convert(x.getChild(1)));
    }

    public ABSAndBoolExp convert(AndBoolExp x) {
        return new ABSAndBoolExp((IABSPureExpression) convert(x.getChild(0)),
                (IABSPureExpression) convert(x.getChild(1)));
    }

    public ABSOrBoolExp convert(OrBoolExp x) {
        return new ABSOrBoolExp((IABSPureExpression) convert(x.getChild(0)),
                (IABSPureExpression) convert(x.getChild(1)));
    }

    public ABSVariableDeclarationStatement convert(VarDeclStmt x) {
        KeYJavaType type = lookupType(x.getVarDecl().getType().getQualifiedName());
        LocationVariable localVar = new LocationVariable(new ProgramElementName(x.getVarDecl().getName()), type);
        IABSExpression initExp = (IABSExpression) convert(x.getVarDecl().getInitExp());
        return new ABSVariableDeclarationStatement(new ABSTypeReference(type), localVar, initExp);
    }
    
    protected KeYJavaType lookupType(String qualifiedName) {
        return services.getProgramInfo().getKeYJavaType(qualifiedName);
    }

    protected abstract IProgramVariable lookupLocalVariable(String name);

    protected abstract IProgramVariable lookupFieldVariable(String name);

}