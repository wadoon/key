package recoder.convenience;

import recoder.java.CompilationUnit;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

import java.util.List;

public class ForestWalker extends AbstractTreeWalker {
    List<CompilationUnit> unitList;

    int unitIndex;

    public ForestWalker(List<CompilationUnit> units) {
        super(units.size() * 8);
        this.unitList = units;
        this.unitIndex = 0;
        if (this.unitList.size() > 0)
            reset(this.unitList.get(this.unitIndex));
    }

    public boolean next() {
        if (this.count == 0) {
            this.current = null;
            if (this.unitIndex >= this.unitList.size() - 1)
                return false;
            this.unitIndex++;
            reset(this.unitList.get(this.unitIndex));
            return next();
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

    public boolean equals(Object x) {
        if (!(x instanceof ForestWalker))
            return false;
        ForestWalker fw = (ForestWalker) x;
        if (!super.equals(x))
            return false;
        return (fw.unitIndex == this.unitIndex && fw.unitList.equals(this.unitList));
    }
}
