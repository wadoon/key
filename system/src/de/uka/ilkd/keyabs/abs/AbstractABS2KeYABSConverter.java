package de.uka.ilkd.keyabs.abs;

import java.math.BigInteger;

import abs.frontend.ast.*;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.keyabs.abs.expression.*;
import de.uka.ilkd.keyabs.logic.sort.programSV.ABSFieldSV;

public abstract class AbstractABS2KeYABSConverter {

    private final IServices services;

    protected Namespace<IProgramVariable> pv = new Namespace<IProgramVariable>();

    public AbstractABS2KeYABSConverter(IServices services) {
        this.services = services;
    }

    public AbstractABS2KeYABSConverter(IServices services,
            Namespace<IProgramVariable> pv) {
        this.services = services;
        this.pv = pv;
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
            result = convert((Binary) x);
        } else if (x instanceof VarDeclStmt) {
            result = convert((VarDeclStmt) x);
        } else if (x instanceof NullExp) {
            result = new ABSNullExp();
        } else if (x instanceof ThisExp) {
            result = new ThisExpression();
        } else if (x instanceof ExpressionStmt
                && !(x.getChild(1) instanceof IncompleteAccess)) {
            result = convert(((ExpressionStmt) x).getExp());
        } else if (x instanceof AsyncCall) {
            result = convert((AsyncCall) x);
        } else if (x instanceof DataConstructorExp) {
            result = convert((DataConstructorExp) x);
        } else if (x instanceof IntLiteral) {
            result = convert((IntLiteral) x);
        } else if (x instanceof IfStmt) {
            result = convert((IfStmt) x);
        } else if (x instanceof WhileStmt) {
            result = convert((WhileStmt) x);
        } else if (x instanceof MinusExp) {
            result = convert((MinusExp) x);
        } else if (x instanceof AwaitStmt) {
            result = convert((AwaitStmt) x);            
        } else if (x instanceof FnApp) {
            result = convert((FnApp)x);
        } else if (x instanceof GetExp) {
            result = convert((GetExp)x);
        } else if (x instanceof ReturnStmt) {
            result = convert((ReturnStmt)x);
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
        } else if (x instanceof EqExp) {
            result = convert((EqExp) x);
        } else if (x instanceof NotEqExp) {
            result = convert((NotEqExp) x);
        } else if (x instanceof GTEQExp) {
            result = convert((GTEQExp) x);
        } else if (x instanceof GTExp) {
            result = convert((GTExp) x);
        } else if (x instanceof LTEQExp) {
            result = convert((LTEQExp) x);
        } else if (x instanceof LTExp) {
            result = convert((LTExp) x);
        }
        return result;
    }

    protected ProgramElement requestConversion(ASTNode<?> x) {
        return null;
    }

    protected ProgramElement convert(SchemaVariable value) {
        return (ProgramSV) value;
    }

    public ABSAsyncMethodCall convert(AsyncCall x) {
        IABSPureExpression callee = (IABSPureExpression) convert(x.getCallee());
        ProgramElementName methodName = new ProgramElementName(x.getMethod());

        IABSPureExpression[] arguments = new IABSPureExpression[x.getNumParam()];

        int i = 0;
        for (PureExp arg : x.getParamList()) {
            arguments[i] = (IABSPureExpression) convert(arg);
            i++;
        }

        return new ABSAsyncMethodCall(callee, methodName, arguments);
    }

    public ABSStatementBlock convert(Block x) {
        IABSStatement[] bodyStmnts = new IABSStatement[x.getNumStmt()];
        pv = pv.extended(ImmutableSLList.<IProgramVariable> nil());
        for (int i = 0; i < x.getNumStmt(); i++) {
            bodyStmnts[i] = (IABSStatement) convert(x.getStmt(i));
        }
        pv = pv.parent();
        return new ABSStatementBlock(bodyStmnts);
    }

    public CopyAssignment convert(AssignStmt x) {
        IABSLocationReference lhs = (IABSLocationReference) convert(x.getVar());
        
        IABSExpression rhs = (IABSExpression) convert(x.getValue());
        return new CopyAssignment(lhs, rhs);
    }

    public ABSIfStatement convert(IfStmt x) {
        IABSPureExpression cond = (IABSPureExpression) convert(x.getCondition());
        IABSStatement _then = (IABSStatement) convert(x.getThen());
        IABSStatement _else = x.hasElse() ? (IABSStatement) convert(x.getElse())
                : null;

        return new ABSIfStatement(cond, _then, _else);
    }

    public ABSWhileStatement convert(WhileStmt x) {
        IABSPureExpression cond = (IABSPureExpression) convert(x.getCondition());
        IABSStatement body = (IABSStatement) convert(x.getBody());

        return new ABSWhileStatement(cond, body);

    }

    public ABSAwaitStatement convert(AwaitStmt x) {
	
	IABSPureExpression cond;
	boolean claim = false;
	if (x.getGuard() instanceof ExpGuard) {
	    cond = (IABSPureExpression) convert(((ExpGuard)x.getGuard()).getPureExp());
	} else if (x.getGuard() instanceof ClaimGuard) {
	    cond = (IABSPureExpression) convert(((ClaimGuard)x.getGuard()).getVar());
	    claim = true;
	} else {
	    throw new RuntimeException("Guards of type " + x.getClass() + "(" + x.getGuard() + 
		    ") are not yet supported.");
	}
        return claim ? new ABSAwaitClaimStatement(cond) : new ABSAwaitStatement(cond);
    }

    
    public ABSFieldReference convert(FieldUse fieldUse) {
        IProgramVariable var = lookupFieldVariable(fieldUse.getDecl().getContextDecl().qualifiedName(), fieldUse.getName());
        return new ABSFieldReference(var);
    }

    public Expression convert(VarUse varUse) {
        IProgramVariable var = lookupLocalVariable(varUse.getName());
        if (var == null || var.sort() instanceof ABSFieldSV) {
            var = lookupFieldVariable(varUse.getDecl().getContextDecl().qualifiedName(), varUse.getName());
            return new ABSFieldReference(var);
        }
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

    public ABSEqExp convert(EqExp x) {
        return new ABSEqExp((IABSPureExpression) convert(x.getChild(0)),
                (IABSPureExpression) convert(x.getChild(1)));
    }

    public ABSNotEqExp convert(NotEqExp x) {
        return new ABSNotEqExp((IABSPureExpression) convert(x.getChild(0)),
                (IABSPureExpression) convert(x.getChild(1)));
    }

    public ABSGTExp convert(GTExp x) {
        return new ABSGTExp((IABSPureExpression) convert(x.getChild(0)),
                (IABSPureExpression) convert(x.getChild(1)));
    }

    public ABSGEQExp convert(GTEQExp x) {
        return new ABSGEQExp((IABSPureExpression) convert(x.getChild(0)),
                (IABSPureExpression) convert(x.getChild(1)));
    }

    public ABSLTExp convert(LTExp x) {
        return new ABSLTExp((IABSPureExpression) convert(x.getChild(0)),
                (IABSPureExpression) convert(x.getChild(1)));
    }

    public ABSLEQExp convert(LTEQExp x) {
        return new ABSLEQExp((IABSPureExpression) convert(x.getChild(0)),
                (IABSPureExpression) convert(x.getChild(1)));
    }

    public ABSIntLiteral convert(IntLiteral x) {
        return new ABSIntLiteral(new BigInteger(x.getContent()));
    }

    public ABSFnApp convert(FnApp x) {
        ProgramElementName fctName = new ProgramElementName(x.getName(), x.getDecl().moduleName());
        IABSPureExpression[] arguments = new IABSPureExpression[x.getNumParam()];

        int i = 0;
        for (PureExp arg : x.getParamList()) {
            arguments[i] = (IABSPureExpression) convert(arg);
            i++;
        }
        return new ABSFnApp(fctName, arguments);
    }

    public IABSPureExpression convert(MinusExp x) {
        if (x.getChild(0) instanceof IntLiteral) {
            return new ABSIntLiteral(new BigInteger("-"
                    + ((IntLiteral) x.getChild(0)).getContent()));
        }
        return new ABSMinusExp((IABSPureExpression) convert(x.getChild(0)));
    }

    public ABSDataConstructorExp convert(DataConstructorExp x) {
        ProgramElementName pen = new ProgramElementName(x.getDataConstructor()
                .getName(), x.getDataConstructor().getDataTypeDecl()
                .moduleName()
                + "." + x.getDataConstructor().getDataTypeDecl().getName());

        IABSPureExpression[] args = new IABSPureExpression[x.getNumParam()];
        for (int i = 0; i < x.getNumParam(); i++) {
            args[i] = (IABSPureExpression) convert(x.getParam(i));
        }
        return new ABSDataConstructorExp(pen, args);
    }

    public ABSVariableDeclarationStatement convert(VarDeclStmt x) {
        KeYJavaType type = lookupType(x.getVarDecl().getType()
                .getQualifiedName());
        LocationVariable localVar = new LocationVariable(
                new ProgramElementName(x.getVarDecl().getName()), type);
        pv.add(localVar);
        IABSExpression initExp = null;
        if (x.getVarDecl().hasInitExp()) {
            initExp = (IABSExpression) convert(x.getVarDecl().getInitExp());
        }
        return new ABSVariableDeclarationStatement(new ABSTypeReference(type),
                localVar, initExp);
    }

    public ABSGetExp convert(GetExp x) {
        return new ABSGetExp((IABSPureExpression)convert(x.getPureExp()));
    }

    public ABSReturnStatement convert(ReturnStmt x) {
        return new ABSReturnStatement((IABSExpression)convert(x.getRetExp()));
    }

    protected KeYJavaType lookupType(String qualifiedName) {
        return services.getProgramInfo().getKeYJavaType(qualifiedName);
    }

    protected abstract IProgramVariable lookupLocalVariable(String name);

    protected abstract IProgramVariable lookupFieldVariable(String className, String name);

}