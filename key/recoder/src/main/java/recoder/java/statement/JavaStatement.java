package recoder.java.statement;

import recoder.java.*;

public abstract class JavaStatement extends JavaNonTerminalProgramElement implements Statement {
    protected StatementContainer parent;

    public JavaStatement() {
    }

    protected JavaStatement(JavaStatement proto) {
        super(proto);
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
}
