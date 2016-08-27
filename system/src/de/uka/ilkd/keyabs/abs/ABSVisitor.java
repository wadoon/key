package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.visitor.ProgramVisitor;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.keyabs.abs.expression.ABSAddExp;
import de.uka.ilkd.keyabs.abs.expression.ABSAndBoolExp;
import de.uka.ilkd.keyabs.abs.expression.ABSDataConstructorExp;
import de.uka.ilkd.keyabs.abs.expression.ABSDivExp;
import de.uka.ilkd.keyabs.abs.expression.ABSEqExp;
import de.uka.ilkd.keyabs.abs.expression.ABSFnApp;
import de.uka.ilkd.keyabs.abs.expression.ABSGEQExp;
import de.uka.ilkd.keyabs.abs.expression.ABSGTExp;
import de.uka.ilkd.keyabs.abs.expression.ABSIntLiteral;
import de.uka.ilkd.keyabs.abs.expression.ABSLEQExp;
import de.uka.ilkd.keyabs.abs.expression.ABSLTExp;
import de.uka.ilkd.keyabs.abs.expression.ABSMinusExp;
import de.uka.ilkd.keyabs.abs.expression.ABSModExp;
import de.uka.ilkd.keyabs.abs.expression.ABSMultExp;
import de.uka.ilkd.keyabs.abs.expression.ABSNegExp;
import de.uka.ilkd.keyabs.abs.expression.ABSNewExpression;
import de.uka.ilkd.keyabs.abs.expression.ABSNotEqExp;
import de.uka.ilkd.keyabs.abs.expression.ABSNullExp;
import de.uka.ilkd.keyabs.abs.expression.ABSOrBoolExp;
import de.uka.ilkd.keyabs.abs.expression.ABSSubExp;

public interface ABSVisitor extends ProgramVisitor {

    void performActionOnABSFieldReference(ABSFieldReference x);

    void performActionOnABSLocalVariableReference(ABSLocalVariableReference x);

    void performActionOnThisExpression(ThisExpression x);

    void performActionOnCopyAssignment(ABSCopyAssignment x);

    void performActionOnABSStatementBlock(ABSStatementBlock x);

    void performActionOnProgramMetaConstruct(ProgramTransformer<ABSServices> x);

    void performActionOnABSAddExp(ABSAddExp x);

    void performActionOnABSSubExp(ABSSubExp x);

    void performActionOnABSMultExp(ABSMultExp x);
	
	void performActionOnABSDivExp(ABSDivExp x);

	void performActionOnABSModExp(ABSModExp x);

    void performActionOnABSAndBoolExp(ABSAndBoolExp x);

    void performActionOnABSOrBoolExp(ABSOrBoolExp x);

    void performActionOnABSTypeReference(ABSTypeReference x);

    void performActionOnABSVariableDeclarationStatement(
            ABSVariableDeclarationStatement x);

    void performActionOnABSAsyncMethodCall(ABSAsyncMethodCall x);

    void performActionOnABSSyncMethodCall(ABSSyncMethodCall x);

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

    void performActionOnABSWhileStatement(ABSWhileStatement x);

    void performActionOnABSAwaitStatement(ABSAwaitStatement x);

    void performActionOnABSAwaitClaimStatement(ABSAwaitClaimStatement x);

    void performActionOnABSFnApp(ABSFnApp x);

    void performActionOnABSGetExp(ABSGetExp x);
    
    void performActionOnABSCaseStatement(ABSCaseStatement x);

    void performActionOnABSReturnStatement(ABSReturnStatement x);

    void performActionOnABSMethodFrame(ABSMethodFrame x);

    void performActionOnABSMethodLabel(IABSMethodLabel x);

    void performActionOnABSExecutionContext(ABSExecutionContext x);

    void performActionOnABSNewExp(ABSNewExpression absNewExpression);

	void performActionOnABSCaseBranchStatement(ABSCaseBranchStatement x);

	void performActionOnABSLiteralPattern(ABSLiteralPattern x);

	void performActionOnABSConstructorPattern(ABSConstructorPattern x);
	
  //void performActionOnABSPatternVar(ABSPatternVar x);	
    
  //void performActionOnABSPatternVarUse(ABSPatternVarUse x);
	
    void performActionOnABSUnderscorePattern(ABSUnderscorePattern x);

	void performActionOnABSDataConstructor(ABSDataConstructor x);

	void performActionOnABSAssertStatement(ABSAssertStatement x);

	void performActionOnABSNegExp(ABSNegExp x);

	void performActionOnABSPatternVar(ABSPatternVar x);

	void performActionOnABSPatternVarUse(ABSPatternVarUse x);



}
