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

    void performActionOnABSAddExp(ABSAddExp x);

    void performActionOnABSMultExp(ABSMultExp x);

    void performActionOnABSAndBoolExp(ABSAndBoolExp x);

    void performActionOnABSOrBoolExp(ABSOrBoolExp x);

    void performActionOnABSTypeReference(ABSTypeReference x);

    void performActionOnABSVariableDeclarationStatement(ABSVariableDeclarationStatement x);

    void performActionOnABSAsyncMethodCall(ABSAsyncMethodCall x);

    void performActionOnABSNullExp(ABSNullExp x);

    void performActionOnABSDataConstructorExp(ABSDataConstructorExp x);

    void performActionOnABSIntLiteral(ABSIntLiteral x);

}
