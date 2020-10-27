package recoder.convenience;

import recoder.ModelElement;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

public class CustomTreeWalker extends TreeWalker {
    boolean isReportingReturns = false;

    ModelElementFilter childFilter = null;

    ModelElementFilter parentFilter = null;

    boolean isReturning = false;

    protected CustomTreeWalker(int initialStackCapacity) {
        super(initialStackCapacity);
    }

    public CustomTreeWalker(ProgramElement root) {
        super(root);
    }

    public CustomTreeWalker(ProgramElement root, int initialStackCapacity) {
        super(root, initialStackCapacity);
    }

    public boolean isReportingReturns() {
        return this.isReportingReturns;
    }

    public void setReportingReturns(boolean yes) {
        this.isReportingReturns = yes;
    }

    public boolean isReturning() {
        return this.isReturning;
    }

    public void setParentFilter(ModelElementFilter filter) {
        this.parentFilter = filter;
    }

    public void setChildFilter(ModelElementFilter filter) {
        this.childFilter = filter;
    }

    public boolean next() {
        if (this.count == 0) {
            this.current = null;
            this.isReturning = true;
            return false;
        }
        this.current = this.stack[--this.count];
        if (this.current == null) {
            if (this.isReportingReturns) {
                this.current = this.stack[--this.count];
                this.isReturning = true;
                return true;
            }
            do {
                this.count--;
                if (this.count == 0) {
                    this.current = null;
                    this.isReturning = true;
                    return false;
                }
                this.current = this.stack[--this.count];
            } while (this.current == null);
        }
        if (this.current instanceof NonTerminalProgramElement) {
            NonTerminalProgramElement nt = (NonTerminalProgramElement) this.current;
            int s = nt.getChildCount();
            if (this.count + s + 2 >= this.stack.length) {
                ProgramElement[] newStack = new ProgramElement[Math.max(this.stack.length * 2, this.count + s + 2)];
                System.arraycopy(this.stack, 0, newStack, 0, this.count);
                this.stack = newStack;
            }
            this.stack[this.count++] = nt;
            this.stack[this.count++] = null;
            if (this.parentFilter == null || this.parentFilter.accept(nt))
                if (this.childFilter == null) {
                    for (int i = s - 1; i >= 0; i--)
                        this.stack[this.count++] = nt.getChildAt(i);
                } else {
                    for (int i = s - 1; i >= 0; i--) {
                        ProgramElement e = nt.getChildAt(i);
                        if (this.childFilter.accept(e))
                            this.stack[this.count++] = e;
                    }
                }
            this.isReturning = false;
        } else {
            this.isReturning = true;
        }
        return true;
    }
}
