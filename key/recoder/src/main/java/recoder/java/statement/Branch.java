package recoder.java.statement;

import recoder.java.JavaNonTerminalProgramElement;
import recoder.java.JavaProgramElement;
import recoder.java.NonTerminalProgramElement;
import recoder.java.StatementContainer;

public abstract class Branch extends JavaNonTerminalProgramElement implements StatementContainer {
    protected BranchStatement parent;

    public Branch() {
    }

    protected Branch(Branch proto) {
        super(proto);
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public BranchStatement getParent() {
        return this.parent;
    }
}
