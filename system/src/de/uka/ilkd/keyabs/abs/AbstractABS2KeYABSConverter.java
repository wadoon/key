package de.uka.ilkd.keyabs.abs;

import java.math.BigInteger;
import java.util.LinkedList;

import abs.frontend.ast.ASTNode;
import abs.frontend.ast.AddExp;
import abs.frontend.ast.AndBoolExp;
import abs.frontend.ast.AssignStmt;
import abs.frontend.ast.AsyncCall;
import abs.frontend.ast.AwaitStmt;
import abs.frontend.ast.AssertStmt;
import abs.frontend.ast.Binary;
import abs.frontend.ast.Block;
import abs.frontend.ast.CaseBranchStmt;
import abs.frontend.ast.CaseStmt;
import abs.frontend.ast.ClaimGuard;
import abs.frontend.ast.ConstructorPattern;
import abs.frontend.ast.DataConstructor;
import abs.frontend.ast.DataConstructorExp;
import abs.frontend.ast.EqExp;
import abs.frontend.ast.ExpGuard;
import abs.frontend.ast.ExpressionStmt;
import abs.frontend.ast.FieldUse;
import abs.frontend.ast.FnApp;
import abs.frontend.ast.GTEQExp;
import abs.frontend.ast.GTExp;
import abs.frontend.ast.GetExp;
import abs.frontend.ast.IfStmt;
import abs.frontend.ast.IncompleteAccess;
import abs.frontend.ast.IntLiteral;
import abs.frontend.ast.LTEQExp;
import abs.frontend.ast.LTExp;
import abs.frontend.ast.LiteralPattern;
import abs.frontend.ast.MinusExp;
import abs.frontend.ast.MultExp;
import abs.frontend.ast.NewExp;
import abs.frontend.ast.NegExp;
import abs.frontend.ast.NotEqExp;
import abs.frontend.ast.NullExp;
import abs.frontend.ast.OrBoolExp;
import abs.frontend.ast.Pattern;
import abs.frontend.ast.PureExp;
import abs.frontend.ast.ReturnStmt;
import abs.frontend.ast.ThisExp;
import abs.frontend.ast.UnderscorePattern;
import abs.frontend.ast.VarDeclStmt;
import abs.frontend.ast.VarUse;
import abs.frontend.ast.WhileStmt;
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
import de.uka.ilkd.keyabs.abs.expression.ABSAddExp;
import de.uka.ilkd.keyabs.abs.expression.ABSAndBoolExp;
import de.uka.ilkd.keyabs.abs.expression.ABSDataConstructorExp;
import de.uka.ilkd.keyabs.abs.expression.ABSEqExp;
import de.uka.ilkd.keyabs.abs.expression.ABSFnApp;
import de.uka.ilkd.keyabs.abs.expression.ABSGEQExp;
import de.uka.ilkd.keyabs.abs.expression.ABSGTExp;
import de.uka.ilkd.keyabs.abs.expression.ABSIntLiteral;
import de.uka.ilkd.keyabs.abs.expression.ABSLEQExp;
import de.uka.ilkd.keyabs.abs.expression.ABSLTExp;
import de.uka.ilkd.keyabs.abs.expression.ABSLiteralExp;
import de.uka.ilkd.keyabs.abs.expression.ABSMinusExp;
import de.uka.ilkd.keyabs.abs.expression.ABSMultExp;
import de.uka.ilkd.keyabs.abs.expression.ABSNewExpression;
import de.uka.ilkd.keyabs.abs.expression.ABSNotEqExp;
import de.uka.ilkd.keyabs.abs.expression.ABSNullExp;
import de.uka.ilkd.keyabs.abs.expression.ABSNegExp;
import de.uka.ilkd.keyabs.abs.expression.ABSOrBoolExp;
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
        } else if (x instanceof AssertStmt) {
            result = convert((AssertStmt) x);            
        } else if (x instanceof FnApp) {
            result = convert((FnApp)x);
        } else if (x instanceof GetExp) {
            result = convert((GetExp)x);
        } else if (x instanceof ReturnStmt) {
            result = convert((ReturnStmt)x);
        } else if (x instanceof NewExp) {
            result = convert((NewExp)x);
        } else if (x instanceof CaseStmt) {
        	result = convert((CaseStmt)x);
        } else if (x instanceof Pattern){
        	result = convert((Pattern)x);
        } else if (x instanceof DataConstructor){
        	result = convert((DataConstructor)x);
        } else if (x instanceof NegExp){
        	result = convert((NegExp)x);
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
    
    protected ProgramElement convert(Pattern x) {
        ProgramElement result = null;
        if (x instanceof LiteralPattern) {
            result = convert((LiteralPattern) x);
        } else if(x instanceof ConstructorPattern) {
        	result = convert((ConstructorPattern) x);
        }else if (x instanceof UnderscorePattern){
            result = new ABSUnderscorePattern();
        } else {
        	throw new IllegalArgumentException("Conversion of " + x.getClass() + " not yet supported.");
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
    
    public ABSAssertStatement convert(AssertStmt x) {
   	
    	IABSPureExpression cond = (IABSPureExpression) convert(x.getCondition());
	
        return new ABSAssertStatement(cond);
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

    public ABSNegExp convert(NegExp x) {
        return new ABSNegExp((IABSPureExpression) convert(x.getChild(0)));
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

    public ABSLiteralExp convert(IntLiteral x) {
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
        DataConstructor dataConstructor = x.getDataConstructor();
		ProgramElementName pen = createDataConstructorName(dataConstructor);

        IABSPureExpression[] args = new IABSPureExpression[x.getNumParam()];
        for (int i = 0; i < x.getNumParam(); i++) {
            args[i] = (IABSPureExpression) convert(x.getParam(i));
        }
        return new ABSDataConstructorExp(pen, args);
    }

	protected ProgramElementName createDataConstructorName(DataConstructor dataConstructor) {
		return new ProgramElementName(dataConstructor
                .getName(), dataConstructor.getDataTypeDecl()
                .moduleName()
                + "." + dataConstructor.getDataTypeDecl().getName());
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

    public ABSNewExpression convert(NewExp x) {
        ProgramElementName className = new ProgramElementName(x.getClassName(), x.getModuleDecl().getName());
        IABSPureExpression[] arguments = new IABSPureExpression[x.getNumParam()];

        int i = 0;
        for (PureExp arg : x.getParamList()) {
            arguments[i] = (IABSPureExpression) convert(arg);
            i++;
        }
        
        return new ABSNewExpression(className, lookupType(x.getType().getQualifiedName()) , arguments);
    }

    public ABSCaseStatement convert(CaseStmt x) {

    	IABSPureExpression caseExp = (IABSPureExpression) convert(x.getExpr());
    	LinkedList<IABSCaseBranchStatement> branches = new LinkedList<IABSCaseBranchStatement>();

        for (CaseBranchStmt arg : x.getBranchList()) {
            branches.add((IABSCaseBranchStatement)convert(arg));
        }
        
        return new ABSCaseStatement(caseExp, branches);
    }
    
    public ABSCaseBranchStatement convert(CaseBranchStmt x) {

    	IABSPattern pattern = (IABSPattern) convert(x.getLeft());
    	IABSStatement stmt = (IABSStatement) convert(x.getRight());
    	
        return new ABSCaseBranchStatement(pattern, stmt);
    }
    
    public ABSLiteralPattern convert(LiteralPattern x) {
    	return new ABSLiteralPattern((ABSLiteralExp) convert(x.getLiteral()));
    }

    public ABSDataConstructor convert(DataConstructor x) {
    	ProgramElementName dataconstructorName = createDataConstructorName(x);
    	if (x.getConstructorArgs().getNumChild() > 0) {
    		throw new RuntimeException("DataConstructorPattern with arguments not yet supported.");
    	}
    	return new ABSDataConstructor(dataconstructorName);
    }
    
    public ABSConstructorPattern convert(ConstructorPattern x) {
    	return new ABSConstructorPattern(convert(x.getDataConstructor()));
    }
    
    protected KeYJavaType lookupType(String qualifiedName) {
        return services.getProgramInfo().getKeYJavaType(qualifiedName);
    }

    protected abstract IProgramVariable lookupLocalVariable(String name);

    protected abstract IProgramVariable lookupFieldVariable(String className, String name);

}