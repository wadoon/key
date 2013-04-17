package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.keyabs.abs.expression.*;

public abstract class ABSVisitorImpl implements ABSVisitor {

    private ProgramElement root;

    protected ABSVisitorImpl(ProgramElement root) {
        this.root = root;
    }

    protected ProgramElement root() {
        return root;
    }

    /**
     * walks through the AST. While keeping track of the current node
     * 
     * @param node
     *            the JavaProgramElement the walker is at
     */
    protected void walk(ProgramElement node) {
        if (node instanceof NonTerminalProgramElement) {
            NonTerminalProgramElement nonTerminalNode = (NonTerminalProgramElement) node;
            for (int i = 0; i < nonTerminalNode.getChildCount(); i++) {
                if (nonTerminalNode.getChildAt(i) != null) {
                    walk(nonTerminalNode.getChildAt(i));
                }
            }
        }

        // otherwise the node is left, so perform the action
        doAction(node);
    }

    protected void doAction(ProgramElement node) {
        node.visit(this);
    }

    /** starts the walker */
    public void start() {
        walk(root);
    }

    protected void doDefaultAction(ProgramElement x) {
    }

    @Override
    public void performActionOnProgramElementName(ProgramElementName x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnProgramMethod(IProgramMethod x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnSchemaVariable(SchemaVariable x) {
        doDefaultAction((ProgramSV) x);
    }

    @Override
    public void performActionOnProgramVariable(ProgramVariable x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnLocationVariable(LocationVariable x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnProgramConstant(ProgramConstant x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSFieldReference(ABSFieldReference x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSLocalVariableReference(
            ABSLocalVariableReference x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnThisExpression(ThisExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnCopyAssignment(CopyAssignment x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSStatementBlock(ABSStatementBlock x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnProgramMetaConstruct(
            ProgramTransformer<ABSServices> x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSAddExp(ABSAddExp x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSMultExp(ABSMultExp x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSAndBoolExp(ABSAndBoolExp x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSOrBoolExp(ABSOrBoolExp x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSTypeReference(ABSTypeReference x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSVariableDeclarationStatement(
            ABSVariableDeclarationStatement x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSAsyncMethodCall(ABSAsyncMethodCall x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSNullExp(ABSNullExp x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSDataConstructorExp(ABSDataConstructorExp x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSIntLiteral(ABSIntLiteral x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSEqExp(ABSEqExp x) {
        doDefaultAction(x);

    }

    @Override
    public void performActionOnABSNotEqExp(ABSNotEqExp x) {
        doDefaultAction(x);

    }

    @Override
    public void performActionOnABSGEQExp(ABSGEQExp x) {
        doDefaultAction(x);

    }

    @Override
    public void performActionOnABSLTExp(ABSLTExp x) {
        doDefaultAction(x);

    }

    @Override
    public void performActionOnABSLEQExp(ABSLEQExp x) {
        doDefaultAction(x);

    }

    @Override
    public void performActionOnABSGTExp(ABSGTExp x) {
        doDefaultAction(x);

    }

    @Override
    public void performActionOnABSIfStatement(ABSIfStatement x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSAwaitStatement(ABSAwaitStatement x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSAwaitClaimStatement(ABSAwaitClaimStatement x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSWhileStatement(ABSWhileStatement x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSContextStatementBlock(
            ABSContextStatementBlock x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSMinusExp(ABSMinusExp x) {
        doDefaultAction(x);
    }
    
    @Override
    public void performActionOnABSFnApp(ABSFnApp x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSGetExp(ABSGetExp x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSReturnStatement(ABSReturnStatement x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSMethodFrame(ABSMethodFrame x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSMethodLabel(IABSMethodLabel x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnABSExecutionContext(ABSExecutionContext x) {
        doDefaultAction(x);
    }


}
