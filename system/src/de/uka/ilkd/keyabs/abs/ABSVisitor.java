package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.visitor.ProgramVisitor;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;

public interface ABSVisitor extends ProgramVisitor {

    void performActionOnABSFieldReference(ABSFieldReference x);

    void performActionOnABSLocalVariableReference(ABSLocalVariableReference x);

    void performActionOnThisExpression(ThisExpression x);

    void performActionOnCopyAssignment(CopyAssignment x);

    void performActionABSStatementBlock(ABSStatementBlock x);

    void performActionOnProgramMetaConstruct(ProgramTransformer<ABSServices> x);

    void performActionOnABSAddExp(ABSAddExp absAddExp);

    void performActionOnABSMultExp(ABSMultExp absMultExp);

    void performActionOnABSAndBoolExp(ABSAndBoolExp absAndBoolExp);

    void performActionOnABSOrBoolExp(ABSOrBoolExp absOrBoolExp);
}
