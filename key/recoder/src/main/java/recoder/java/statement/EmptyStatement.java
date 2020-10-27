package recoder.java.statement;

import recoder.java.*;

public class EmptyStatement extends JavaProgramElement implements Statement, TerminalProgramElement {
    private static final long serialVersionUID = 7235639345998336043L;

    protected StatementContainer parent;

    public EmptyStatement() {
    }

    protected EmptyStatement(EmptyStatement proto) {
        super(proto);
    }

    public EmptyStatement deepClone() {
        return new EmptyStatement(this);
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public StatementContainer getStatementContainer() {
        return this.parent;
    }

    public void setStatementContainer(StatementContainer c) {
        this.parent = c;
    }

    public void accept(SourceVisitor v) {
        v.visitEmptyStatement(this);
    }
}
