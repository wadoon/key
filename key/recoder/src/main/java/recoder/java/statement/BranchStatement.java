package recoder.java.statement;

import recoder.java.NonTerminalProgramElement;

public abstract class BranchStatement extends JavaStatement implements NonTerminalProgramElement {
    public BranchStatement() {
    }

    protected BranchStatement(BranchStatement proto) {
        super(proto);
    }

    public abstract int getBranchCount();

    public abstract Branch getBranchAt(int paramInt);
}
