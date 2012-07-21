package de.uka.ilkd.keyabs.pp;

import java.io.IOException;

import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.keyabs.abs.ABSFieldReference;
import de.uka.ilkd.keyabs.abs.ABSLocalVariableReference;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.ABSStatementBlock;
import de.uka.ilkd.keyabs.abs.ABSVisitor;
import de.uka.ilkd.keyabs.abs.CopyAssignment;
import de.uka.ilkd.keyabs.abs.ThisExpression;

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
        // TODO Auto-generated method stub

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

}
