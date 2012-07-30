package de.uka.ilkd.keyabs.pp;

import java.io.IOException;

import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.keyabs.abs.ABSAsyncMethodCall;
import de.uka.ilkd.keyabs.abs.ABSFieldReference;
import de.uka.ilkd.keyabs.abs.ABSLocalVariableReference;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.ABSStatementBlock;
import de.uka.ilkd.keyabs.abs.ABSTypeReference;
import de.uka.ilkd.keyabs.abs.ABSVariableDeclarationStatement;
import de.uka.ilkd.keyabs.abs.ABSVisitor;
import de.uka.ilkd.keyabs.abs.CopyAssignment;
import de.uka.ilkd.keyabs.abs.ThisExpression;
import de.uka.ilkd.keyabs.abs.expression.ABSAddExp;
import de.uka.ilkd.keyabs.abs.expression.ABSAndBoolExp;
import de.uka.ilkd.keyabs.abs.expression.ABSDataConstructorExp;
import de.uka.ilkd.keyabs.abs.expression.ABSEqExp;
import de.uka.ilkd.keyabs.abs.expression.ABSGEQExp;
import de.uka.ilkd.keyabs.abs.expression.ABSGTExp;
import de.uka.ilkd.keyabs.abs.expression.ABSIntLiteral;
import de.uka.ilkd.keyabs.abs.expression.ABSLEQExp;
import de.uka.ilkd.keyabs.abs.expression.ABSLTExp;
import de.uka.ilkd.keyabs.abs.expression.ABSMultExp;
import de.uka.ilkd.keyabs.abs.expression.ABSNotEqExp;
import de.uka.ilkd.keyabs.abs.expression.ABSNullExp;
import de.uka.ilkd.keyabs.abs.expression.ABSOrBoolExp;

public class ABSProgramPrettyPrinter implements ABSVisitor {


    private LogicPrinter lp;

    public ABSProgramPrettyPrinter(LogicPrinter lp) {
	this.lp = lp;
    }


    @Override
    public void performActionOnProgramElementName(ProgramElementName x) {
	try {
	    lp.printProgramElementName(x);
	} catch (IOException e) {
	    // TODO Auto-generated catch block
	    e.printStackTrace();
	}
    }

    @Override
    public void performActionOnProgramMethod(IProgramMethod x) {
	// TODO Auto-generated method stub

    }

    @Override
    public void performActionOnSchemaVariable(SchemaVariable x) {
    }

    @Override
    public void performActionOnProgramVariable(ProgramVariable x) {
	try {
	    lp.printProgramVariable(x);
	} catch (IOException e) {
	    e.printStackTrace();
	}
    }

    @Override
    public void performActionOnLocationVariable(LocationVariable x) {
	try {
	    lp.printLocationVariable(x);
	} catch (IOException e) {
	    // TODO Auto-generated catch block
	    e.printStackTrace();
	}
    }

    @Override
    public void performActionOnProgramConstant(ProgramConstant x) {
    }

    @Override
    public void performActionOnABSFieldReference(ABSFieldReference x) {
	try {
	    lp.printABSFieldReference(x);
	} catch (IOException e) {
	    // TODO Auto-generated catch block
	    e.printStackTrace();
	}
    }

    @Override
    public void performActionOnABSLocalVariableReference(
	    ABSLocalVariableReference x) {
	try {
	    lp.printABSLocalVariableReference(x);
	} catch (IOException e) {
	    // TODO Auto-generated catch block
	    e.printStackTrace();
	}
    }

    @Override
    public void performActionOnThisExpression(ThisExpression x) {
	try {
	    lp.printThisExpression(x);
	} catch (IOException e) {
	    // TODO Auto-generated catch block
	    e.printStackTrace();
	}
    }

    @Override
    public void performActionOnCopyAssignment(CopyAssignment x) {
	try {
	    lp.printABSCopyAssignment(x);
	} catch (IOException e) {
	    // TODO Auto-generated catch block
	    e.printStackTrace();
	}
    }

    @Override
    public void performActionABSStatementBlock(ABSStatementBlock x) {
	try {
	    lp.printABSStatementBlock(x);
	} catch (IOException e) {
	    // TODO Auto-generated catch block
	    e.printStackTrace();
	}
    }

    @Override
    public void performActionOnProgramMetaConstruct(
	    ProgramTransformer<ABSServices> x) {
	// TODO Auto-generated method stub

    }


    @Override
    public void performActionOnABSAddExp(ABSAddExp x) {
	try {
	    lp.printABSBinaryOpExp(x, "+");
	} catch (IOException e) {
	    e.printStackTrace();
	} 
    }


    @Override
    public void performActionOnABSMultExp(ABSMultExp x) {
	try {
	    lp.printABSBinaryOpExp(x, "*");
	} catch (IOException e) {
	    e.printStackTrace();
	} 
    }


    @Override
    public void performActionOnABSAndBoolExp(ABSAndBoolExp x) {
	try {
	    lp.printABSBinaryOpExp(x, "&&");
	} catch (IOException e) {
	    e.printStackTrace();
	} 
    }


    @Override
    public void performActionOnABSOrBoolExp(ABSOrBoolExp x) {
	try {
	    lp.printABSBinaryOpExp(x, "||");
	} catch (IOException e) {
	    e.printStackTrace();
	} 
    }


    @Override
    public void performActionOnABSTypeReference(ABSTypeReference x) {
	try {
	    lp.printABSTypeReference(x);
	} catch (IOException e) {
	    e.printStackTrace();
	}         
    }


    @Override
    public void performActionOnABSVariableDeclarationStatement(
	    ABSVariableDeclarationStatement x) {
	try {
	    lp.printABSVariableDeclarationStatement(x);
	} catch (IOException e) {
	    e.printStackTrace();
	} 
    }


    @Override
    public void performActionOnABSAsyncMethodCall(ABSAsyncMethodCall x) {
	try {
	    lp.printABSAsyncMethodCall(x);
	} catch (IOException e) {
	    e.printStackTrace();
	} 		
    }


    @Override
    public void performActionOnABSNullExp(ABSNullExp x) {
	try {
	    lp.printABSNullExp(x);
	} catch (IOException e) {
	    e.printStackTrace();
	} 		
    }


    @Override
    public void performActionOnABSDataConstructorExp(ABSDataConstructorExp x) {
	try {
	    lp.printABSDataConstructorExp(x);
	} catch (IOException e) {
	    e.printStackTrace();
	} 	
    }


    @Override
    public void performActionOnABSIntLiteral(ABSIntLiteral x) {
	try {
	    lp.printABSIntLiteral(x);
	} catch (IOException e) {
	    e.printStackTrace();
	}     
    }


    @Override
    public void performActionOnABSEqExp(ABSEqExp x) {
        try {
            lp.printABSBinaryOpExp(x, "==");
        } catch (IOException e) {
            e.printStackTrace();
        }     
    }


    @Override
    public void performActionOnABSNotEqExp(ABSNotEqExp x) {
        try {
            lp.printABSBinaryOpExp(x, "!=");
        } catch (IOException e) {
            e.printStackTrace();
        }     
    }

    @Override
    public void performActionOnABSGTExp(ABSGTExp x) {
        try {
            lp.printABSBinaryOpExp(x, ">");
        } catch (IOException e) {
            e.printStackTrace();
        }     
    }

    @Override
    public void performActionOnABSGEQExp(ABSGEQExp x) {
        try {
            lp.printABSBinaryOpExp(x, ">=");
        } catch (IOException e) {
            e.printStackTrace();
        }     
    }


    @Override
    public void performActionOnABSLTExp(ABSLTExp x) {
        try {
            lp.printABSBinaryOpExp(x, "<");
        } catch (IOException e) {
            e.printStackTrace();
        }     
    }


    @Override
    public void performActionOnABSLEQExp(ABSLEQExp x) {
        try {
            lp.printABSBinaryOpExp(x, "<=");
        } catch (IOException e) {
            e.printStackTrace();
        }     
    }



}
