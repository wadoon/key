package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.keyabs.abs.expression.*;

import java.util.Stack;

public abstract class ABSModificationVisitor extends ABSVisitorImpl implements
        IProgramASTModifyingVisitor, ABSVisitor {

    protected static final Boolean CHANGED = Boolean.TRUE;

    boolean preservesPositionInfo = true;

    /**  */
    protected Stack<ExtList> stack = new Stack<ExtList>();

    public ABSModificationVisitor(ProgramElement root) {
        super(root);
    }

    /** starts the walker */
    @Override
    public void start() {
        ExtList l = new ExtList();
        stack.push(l);
        super.start();
    }

    @Override
    protected void walk(ProgramElement node) {
        ExtList l = new ExtList();
        stack.push(l);
        super.walk(node);
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.keyabs.abs.IProgramASTModifyingVisitor#result()
     */
    @Override
    public ProgramElement result() {
        ExtList result = stack.peek();
        if (result.getFirst() == CHANGED) {
            result.removeFirst();
        }
        return (ProgramElement) result.get(0);
    }

    protected void changed() {
        ExtList list = stack.peek();
        if (list.isEmpty() || list.getFirst() != CHANGED) {
            list.addFirst(CHANGED);
        }
    }

    protected void addToTopOfStack(ProgramElement x) {
        if (x != null) {
            ExtList list = stack.peek();
            list.add(x);
        }
    }

    protected void addChild(ProgramElement x) {
        stack.pop();
        addToTopOfStack(x);
    }

    protected void addChildren(ImmutableArray<ProgramElement> arr) {
        stack.pop();
        for (int i = 0, sz = arr.size(); i < sz; i++) {
            addToTopOfStack(arr.get(i));
        }
    }

    protected void addNewChild(ProgramElement x) {
        addChild(x);
        changed();
    }

    @Override
    public void performActionOnProgramElementName(ProgramElementName x) {
        addChild(x);
    }

    @Override
    public void performActionOnProgramMethod(IProgramMethod x) {
        throw new RuntimeException(getClass() + ": To be implemented");
    }

    @Override
    public void performActionOnSchemaVariable(SchemaVariable x) {
        addChild((ProgramSV) x);
    }

    @Override
    public void performActionOnProgramVariable(ProgramVariable x) {
        addChild(x);
    }

    @Override
    public void performActionOnLocationVariable(LocationVariable x) {
        addChild(x);
    }

    @Override
    public void performActionOnProgramConstant(ProgramConstant x) {
        addChild(x);
    }

    @Override
    public void performActionOnABSFieldReference(ABSFieldReference x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSFieldReference(
                    (IProgramVariable) children.get(0)));
        } else {
            addChild(x);
        }
    }

    protected boolean hasChanged() {
        return !stack.peek().isEmpty()
                && stack.peek().getFirst() == Boolean.TRUE;
    }

    @Override
    public void performActionOnABSLocalVariableReference(
            ABSLocalVariableReference x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSLocalVariableReference(
                    (IProgramVariable) children.get(0)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnThisExpression(ThisExpression x) {
        addChild(x);
    }

    @Override
    public void performActionOnABSNullExp(ABSNullExp x) {
        addChild(x);
    }

    @Override
    public void performActionOnCopyAssignment(CopyAssignment x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new CopyAssignment(
                    (IABSLocationReference) children.get(0),
                    (IABSPureExpression) children.get(1)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSAddExp(ABSAddExp x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSAddExp((IABSPureExpression) children.get(0),
                    (IABSPureExpression) children.get(1)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSMultExp(ABSMultExp x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSMultExp((IABSPureExpression) children.get(0),
                    (IABSPureExpression) children.get(1)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSOrBoolExp(ABSOrBoolExp x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSOrBoolExp((IABSPureExpression) children.get(0),
                    (IABSPureExpression) children.get(1)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSAndBoolExp(ABSAndBoolExp x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSAndBoolExp((IABSPureExpression) children.get(0),
                    (IABSPureExpression) children.get(1)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSStatementBlock(ABSStatementBlock x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            final IABSStatement[] body = new IABSStatement[children.size()];
            for (int i = 0; i < children.size(); i++) {
                body[i] = (IABSStatement) children.get(i);
            }
            addNewChild(new ABSStatementBlock(body));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnProgramMetaConstruct(
            ProgramTransformer<ABSServices> x) {
        //
    }

    @Override
    public void performActionOnABSTypeReference(ABSTypeReference x) {
        if (hasChanged()) {
            // should not be called
            assert false;
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSTypeReference(x.getKeYJavaType()));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSVariableDeclarationStatement(
            ABSVariableDeclarationStatement x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            ABSTypeReference typeRef = children
                    .removeFirstOccurrence(ABSTypeReference.class);
            IProgramVariable var = children
                    .removeFirstOccurrence(IProgramVariable.class);
            IABSExpression exp = children
                    .removeFirstOccurrence(IABSExpression.class);
            addNewChild(new ABSVariableDeclarationStatement(typeRef, var, exp));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSAsyncMethodCall(ABSAsyncMethodCall x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            IABSPureExpression caller = children
                    .removeFirstOccurrence(IABSPureExpression.class);
            ProgramElementName methodName = children
                    .removeFirstOccurrence(ProgramElementName.class);

            IABSPureExpression[] arguments = new IABSPureExpression[children
                    .size()];
            for (int i = 0; i < children.size(); i++) {
                arguments[i] = (IABSPureExpression) children.get(i);
            }
            addNewChild(new ABSAsyncMethodCall(caller, methodName, arguments));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSDataConstructorExp(ABSDataConstructorExp x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            ProgramElementName constructor = children
                    .removeFirstOccurrence(ProgramElementName.class);

            IABSPureExpression[] arguments = new IABSPureExpression[children
                    .size()];
            for (int i = 0; i < children.size(); i++) {
                arguments[i] = (IABSPureExpression) children.get(i);
            }
            addNewChild(new ABSDataConstructorExp(constructor, arguments));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSIntLiteral(ABSIntLiteral x) {
        addChild(x);
    }

    @Override
    public void performActionOnABSEqExp(ABSEqExp x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSEqExp((IABSPureExpression) children.get(0),
                    (IABSPureExpression) children.get(1)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSNotEqExp(ABSNotEqExp x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSNotEqExp((IABSPureExpression) children.get(0),
                    (IABSPureExpression) children.get(1)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSGEQExp(ABSGEQExp x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSGEQExp((IABSPureExpression) children.get(0),
                    (IABSPureExpression) children.get(1)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSLTExp(ABSLTExp x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSLTExp((IABSPureExpression) children.get(0),
                    (IABSPureExpression) children.get(1)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSLEQExp(ABSLEQExp x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSLEQExp((IABSPureExpression) children.get(0),
                    (IABSPureExpression) children.get(1)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSGTExp(ABSGTExp x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSGTExp((IABSPureExpression) children.get(0),
                    (IABSPureExpression) children.get(1)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSAwaitStatement(ABSAwaitStatement x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSAwaitStatement((IABSPureExpression) children.get(0)));
        } else {
            addChild(x);
        }
    }
    
    @Override
    public void performActionOnABSAwaitClaimStatement(ABSAwaitClaimStatement x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSAwaitClaimStatement((IABSPureExpression) children.get(0)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSIfStatement(ABSIfStatement x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSIfStatement(
                    (IABSPureExpression) children.get(0),
                    (IABSStatement) children.get(1),
                    children.size() >= 3 ? (IABSStatement) children.get(2)
                            : null));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSWhileStatement(ABSWhileStatement x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSWhileStatement(
                    (IABSPureExpression) children.get(0),
                    (IABSStatement) children.get(1)));
        } else {
            addChild(x);
        }
    }

    
    @Override
    public void performActionOnABSContextStatementBlock(
            ABSContextStatementBlock x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            final IABSStatement[] body = new IABSStatement[children.size()];
            for (int i = 0; i < children.size(); i++) {
                body[i] = (IABSStatement) children.get(i);
            }
            addNewChild(new ABSContextStatementBlock(body));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSMinusExp(ABSMinusExp x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSMinusExp((IABSPureExpression) children.get(0)));
        } else {
            addChild(x);
        }
    }
    
    @Override
    public void performActionOnABSFnApp(ABSFnApp x) {
	if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            ProgramElementName fctName = children
                    .removeFirstOccurrence(ProgramElementName.class);

            IABSPureExpression[] arguments = new IABSPureExpression[children
                    .size()];
            for (int i = 0; i < children.size(); i++) {
                arguments[i] = (IABSPureExpression) children.get(i);
            }
            addNewChild(new ABSFnApp(fctName, arguments));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSGetExp(ABSGetExp x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            addNewChild(new ABSGetExp((IABSPureExpression) children.get(0)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSReturnStatement(ABSReturnStatement x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();

            IABSPureExpression retExp = null;
            if (x.getChildCount() > 0) {
                retExp = (IABSPureExpression) children.get(0);
            }
            addNewChild(new ABSReturnStatement(retExp));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnABSMethodFrame(ABSMethodFrame x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            ABSExecutionContext executionContext = (ABSExecutionContext) children.remove(0);
            ImmutableArray<IABSStatement> body =
                    new ImmutableArray<>(children.collect(IABSStatement.class));
            addNewChild(new ABSMethodFrame(executionContext, body));
        } else {
            addChild(x);
        }
    }


    @Override
    public void performActionOnABSMethodLabel(IABSMethodLabel x) {
        addChild(x);
    }

    @Override
    public void performActionOnABSExecutionContext(ABSExecutionContext x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            ABSMethodLabel methodLabel = (ABSMethodLabel) children.remove(0);
            ABSLocalVariableReference result = (ABSLocalVariableReference) children.remove(0);
            ABSLocalVariableReference future = (ABSLocalVariableReference) children.remove(0);

            addNewChild(new ABSExecutionContext(methodLabel, result, future));
        } else {
            addChild(x);
        }
    }
}
