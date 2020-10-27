package recoder.convenience;

import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

public class TreeWalker extends AbstractTreeWalker {
    protected TreeWalker(int initialStackCapacity) {
        super(initialStackCapacity);
    }

    public TreeWalker(ProgramElement root) {
        super(root);
    }

    public TreeWalker(ProgramElement root, int initialStackCapacity) {
        super(root, initialStackCapacity);
    }

    public void reset(ProgramElement root) {
        super.reset(root);
    }

    public boolean next() {
        if (this.count == 0) {
            this.current = null;
            return false;
        }
        this.current = this.stack[--this.count];
        if (this.current instanceof NonTerminalProgramElement) {
            NonTerminalProgramElement nt = (NonTerminalProgramElement) this.current;
            int s = nt.getChildCount();
            if (this.count + s >= this.stack.length) {
                ProgramElement[] newStack = new ProgramElement[Math.max(this.stack.length * 2, this.count + s)];
                System.arraycopy(this.stack, 0, newStack, 0, this.count);
                this.stack = newStack;
            }
            for (int i = s - 1; i >= 0; i--)
                this.stack[this.count++] = nt.getChildAt(i);
        }
        return true;
    }
}
