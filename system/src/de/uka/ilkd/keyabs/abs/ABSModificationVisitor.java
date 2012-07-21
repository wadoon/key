package de.uka.ilkd.keyabs.abs;

import java.util.Stack;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;

public abstract class ABSModificationVisitor extends ABSVisitorImpl {

    // marker that the elements on the stack need to be composed to a new
    // element
    private final ProgramElement CHANGED = new ABSProgramElement() {
        @Override
        public void visit(ABSVisitor v) {
        }
    };
    private final Stack<ProgramElement> stack = new Stack<ProgramElement>();

    
    public ABSModificationVisitor(ProgramElement root) {
        super(root);
    }
    
    public ProgramElement result() {
        if (stack.peek() == CHANGED) {
            stack.pop();
        }
        return stack.pop();
    }
    
    protected void push(ProgramElement pe) {
        stack.push(pe);
    }

    @Override
    public void performActionOnProgramElementName(ProgramElementName x) {
        push(x);
    }

    @Override
    public void performActionOnProgramMethod(IProgramMethod x) {
        throw new RuntimeException(getClass() + ": To be implemented");
    }

    @Override
    public void performActionOnSchemaVariable(SchemaVariable x) {
        push((ProgramSV) x);
    }

    @Override
    public void performActionOnProgramVariable(ProgramVariable x) {
        push(x);
    }

    @Override
    public void performActionOnLocationVariable(LocationVariable x) {
        push(x);
    }

    @Override
    public void performActionOnProgramConstant(ProgramConstant x) {
        push(x);
    }

    @Override
    public void performActionOnABSFieldReference(ABSFieldReference x) {
        if (changed()) {
            ProgramElement[] children = pop(x.getChildCount());
            pushChanged(new ABSFieldReference((IProgramVariable) children[0]));
        } else {
            push(x);
        }
    }

    protected void pushChanged(ProgramElement x) {
        push(x);
        push(CHANGED);
    }

    @SuppressWarnings("unchecked")
    private <T extends ProgramElement> void pop(T[] children) {
        if (changed())
            stack.pop();
        for (int i = children.length - 1; i >= 0; i--) {
            children[i] = (T) stack.pop();
        }
    }

    private ProgramElement[] pop(int childCount) {
        if (changed())
            stack.pop();
        ProgramElement[] children = new ProgramElement[childCount];
        for (int i = childCount - 1; i >= 0; i--) {
            children[i] = stack.pop();
        }
        return children;
    }

    private boolean changed() {
        return stack.peek() == CHANGED;
    }

    @Override
    public void performActionOnABSLocalVariableReference(
            ABSLocalVariableReference x) {
        if (changed()) {
            ProgramElement[] children = pop(x.getChildCount());
            pushChanged(new ABSLocalVariableReference(
                    (IProgramVariable) children[0]));
        } else {
            push(x);
        }
    }

    @Override
    public void performActionOnThisExpression(ThisExpression x) {
        push(x);
    }

    @Override
    public void performActionOnCopyAssignment(CopyAssignment x) {
        if (changed()) {
            ProgramElement[] children = pop(x.getChildCount());
            pushChanged(new CopyAssignment((IABSLocationReference) children[0],
                    (IABSPureExpression) children[1]));
        } else {
            push(x);
        }
    }

    @Override
    public void performActionABSStatementBlock(ABSStatementBlock x) {
        if (changed()) {
            final IABSStatement[] children = new IABSStatement[x
                    .getChildCount()];
            pop(children);
            pushChanged(new ABSStatementBlock(children));
        } else {
            push(x);
        }
    }
}
