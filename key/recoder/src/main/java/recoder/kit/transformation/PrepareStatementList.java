package recoder.kit.transformation;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.*;
import recoder.kit.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

public class PrepareStatementList extends TwoPassTransformation {
    private Statement statement;

    private StatementBlock block;

    private ASTList<Statement> list;

    private final boolean isVisible;

    public PrepareStatementList(CrossReferenceServiceConfiguration sc, Statement s, boolean isVisible) {
        super(sc);
        if (s == null)
            throw new IllegalArgumentException("Missing statement");
        this.statement = s;
        this.isVisible = isVisible;
    }

    public boolean isVisible() {
        return this.isVisible;
    }

    public ProblemReport analyze() {
        Equivalence equivalence;
        Identity identity = IDENTITY;
        StatementContainer con = this.statement.getStatementContainer();
        if (con == null) {
            this.list = (ASTList<Statement>) new ASTArrayList(this.statement);
        } else {
            this.list = StatementKit.getStatementMutableList(this.statement);
            if (this.list == null) {
                NonTerminalProgramElement parent = this.statement.getASTParent();
                this.block = getProgramFactory().createStatementBlock();
                if (!(parent instanceof StatementContainer))
                    return new IllegalParentContext(parent);
                if (this.statement instanceof recoder.java.declaration.LocalVariableDeclaration) {
                    NoProblem noProblem = NO_PROBLEM;
                } else {
                    equivalence = EQUIVALENCE;
                }
            }
        }
        return setProblemReport(equivalence);
    }

    public void transform() {
        super.transform();
        if (this.block != null) {
            replace(this.statement, this.block);
            if (isVisible())
                this.statement = this.statement.deepClone();
            attach(this.statement, this.block, 0);
            this.list = this.block.getBody();
        }
    }

    public StatementBlock getBlock() {
        return this.block;
    }

    public ASTList<Statement> getStatementList() {
        return this.list;
    }

    public Statement getStatement() {
        return this.statement;
    }

    public static class IllegalParentContext extends Conflict {
        private static final long serialVersionUID = -1995165154877949565L;

        private final NonTerminalProgramElement parent;

        public IllegalParentContext(NonTerminalProgramElement parent) {
            this.parent = parent;
        }

        public NonTerminalProgramElement getParent() {
            return this.parent;
        }
    }
}
