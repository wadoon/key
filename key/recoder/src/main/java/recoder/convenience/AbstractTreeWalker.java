package recoder.convenience;

import recoder.ModelElement;
import recoder.java.ProgramElement;

public abstract class AbstractTreeWalker implements ProgramElementWalker, Cloneable {
    ProgramElement[] stack;

    int count;

    ProgramElement current;

    protected AbstractTreeWalker(int initialStackCapacity) {
        this.stack = new ProgramElement[initialStackCapacity];
    }

    public AbstractTreeWalker(ProgramElement root) {
        this.stack = new ProgramElement[16];
        reset(root);
    }

    public AbstractTreeWalker(ProgramElement root, int initialStackCapacity) {
        this.stack = new ProgramElement[Math.max(8, initialStackCapacity)];
        reset(root);
    }

    protected void reset(ProgramElement root) {
        while (this.count > 0)
            this.stack[--this.count] = null;
        this.stack[this.count++] = this.current = root;
    }

    public boolean next(Class c) {
        while (next()) {
            if (c.isInstance(this.current))
                return true;
        }
        return false;
    }

    public boolean next(ModelElementFilter filter) {
        while (next()) {
            if (filter.accept(this.current))
                return true;
        }
        return false;
    }

    public final ProgramElement getProgramElement() {
        return this.current;
    }

    public AbstractTreeWalker clone() {
        try {
            AbstractTreeWalker here = (AbstractTreeWalker) super.clone();
            here.stack = this.stack.clone();
            return here;
        } catch (CloneNotSupportedException cnse) {
            return null;
        }
    }

    public boolean equals(Object x) {
        if (!(x instanceof AbstractTreeWalker))
            return false;
        AbstractTreeWalker atw = (AbstractTreeWalker) x;
        if (atw.current != this.current)
            return false;
        if (atw.count != this.count)
            return false;
        if (atw.stack == null)
            return (this.stack == null);
        for (int i = 0; i < this.count; i++) {
            if (atw.stack[i] != this.stack[i])
                return false;
        }
        return true;
    }

    public int hashCode() {
        return System.identityHashCode(this.current);
    }

    public abstract boolean next();
}
