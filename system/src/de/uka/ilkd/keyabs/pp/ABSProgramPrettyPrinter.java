package de.uka.ilkd.keyabs.pp;

import java.io.IOException;

import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.keyabs.abs.*;
import de.uka.ilkd.keyabs.abs.ABSReturnStatement;
import de.uka.ilkd.keyabs.abs.expression.*;

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
            e.printStackTrace();
        }
    }

    @Override
    public void performActionOnProgramMethod(IProgramMethod x) {
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
    public void performActionOnABSStatementBlock(ABSStatementBlock x) {
        try {
            lp.printABSStatementBlock(x);
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    @Override
    public void performActionOnABSAwaitStatement(ABSAwaitStatement x) {
        try {
            lp.printABSAwaitStatement(x);
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    @Override
    public void performActionOnABSAwaitClaimStatement(ABSAwaitClaimStatement x) {
        try {
            lp.printABSAwaitStatement(x);
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

    @Override
    public void performActionOnABSIfStatement(ABSIfStatement x) {
        try {
            lp.printABSIfStatement(x);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void performActionOnABSWhileStatement(ABSWhileStatement x) {
        try {
            lp.printABSWhileStatement(x);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    
    @Override
    public void performActionOnABSContextStatementBlock(
            ABSContextStatementBlock x) {
        try {
            lp.printABSContextStatementBlock(x);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void performActionOnABSMinusExp(ABSMinusExp x) {
        try {
            lp.printABSMinusExp(x);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void performActionOnABSFnApp(ABSFnApp x) {
        try {
            lp.printABSFnApp(x);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void performActionOnABSGetExp(ABSGetExp x) {
        try {
            lp.printABSGetExp(x);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void performActionOnABSReturnStatement(ABSReturnStatement x) {
        try {
            lp.printABSReturnStatement(x);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void performActionOnABSMethodFrame(ABSMethodFrame x) {
        try {
            lp.printABSMethodFrame(x);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void performActionOnABSMethodLabel(IABSMethodLabel x) {
        try {
            lp.printABSMethodLabel(x);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void performActionOnABSExecutionContext(ABSExecutionContext x) {
        try {
            lp.printABSExecutionContext(x);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }


}
