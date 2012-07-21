package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;

public class ABSVisitorImpl implements ABSVisitor {

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
        doDefaultAction((ProgramSV)x);
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
    public void performActionABSStatementBlock(ABSStatementBlock x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnProgramMetaConstruct(
            ProgramTransformer<ABSServices> x) {
        doDefaultAction(x);
    }
}
