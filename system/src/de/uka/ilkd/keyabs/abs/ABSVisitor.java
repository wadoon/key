package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.visitor.ProgramVisitor;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
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

    void performActionOnABSEqExp(ABSEqExp x);

    void performActionOnABSNotEqExp(ABSNotEqExp x);

    void performActionOnABSGEQExp(ABSGEQExp x);

    void performActionOnABSLTExp(ABSLTExp x);

    void performActionOnABSLEQExp(ABSLEQExp x);

    void performActionOnABSGTExp(ABSGTExp x);

    void performActionOnABSIfStatement(ABSIfStatement absIfStatement);

    void performActionOnABSContextStatementBlock(ABSContextStatementBlock x);

    void performActionOnABSMinusExp(ABSMinusExp x);

}
