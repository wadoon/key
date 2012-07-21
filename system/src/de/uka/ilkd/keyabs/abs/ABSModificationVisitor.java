package de.uka.ilkd.keyabs.abs;

import java.util.Stack;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.util.ExtList;

public abstract class ABSModificationVisitor extends ABSVisitorImpl {

    protected static final Boolean CHANGED = Boolean.TRUE;

    boolean preservesPositionInfo = true;

    /**  */
    //protected SimpleStackOfExtList stack = new SimpleStackOfExtList();
    protected Stack<ExtList> stack = new Stack<ExtList>();
    
    
    public ABSModificationVisitor(ProgramElement root) {
        super(root);
    }
    
    @Override
    protected void walk(ProgramElement node) {
        if (node instanceof SchemaVariable) {
            System.out.println("===>"+node);
        }
        ExtList l = new ExtList();
        stack.push(l);
        super.walk(node);
    }

    public ProgramElement result() {
        ExtList result = stack.peek();
        if (result.getFirst() == CHANGED) {
            result.removeFirst();
        }
        return (ProgramElement) result.get(0);
    }
    
    /**
     * called if the program element x is unchanged
     */
    protected void unchangedProgramElementAction(ProgramElement x) {
        ExtList changeList = stack.peek();
        if (changeList.size() == 0) {
            addChild(x);
            return;
        }
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            addChild(x);
            changed();
        } else {
            addChild(x);
        }
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
            unchangedProgramElementAction(new ABSFieldReference((IProgramVariable) children.get(0)));
        } else {
            addChild(x);
        }
    }

    private boolean hasChanged() {
        return !stack.peek().isEmpty() && stack.peek().getFirst() == Boolean.TRUE;
    }

    @Override
    public void performActionOnABSLocalVariableReference(
            ABSLocalVariableReference x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            unchangedProgramElementAction(new ABSLocalVariableReference((IProgramVariable) children.get(0)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionOnThisExpression(ThisExpression x) {
        addChild(x);
    }

    @Override
    public void performActionOnCopyAssignment(CopyAssignment x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            unchangedProgramElementAction(new CopyAssignment((IABSLocationReference) children.get(0),
                    (IABSPureExpression) children.get(1)));
        } else {
            addChild(x);
        }
    }

    @Override
    public void performActionABSStatementBlock(ABSStatementBlock x) {
        if (hasChanged()) {
            ExtList children = stack.peek();
            children.removeFirst();
            final IABSStatement[] body = new IABSStatement[children.size()];
            for (int i = 0; i<children.size(); i++) {
                body[i] = (IABSStatement) children.get(i);
            }
            unchangedProgramElementAction(new ABSStatementBlock(body));
        } else {
            addChild(x);
        }
    }
}
