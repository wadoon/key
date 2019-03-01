package edu.kit.iti.formal.psdbg.parser.ast;

import edu.kit.iti.formal.psdbg.parser.ScriptLanguageParser;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import lombok.Getter;
import lombok.Setter;

@Getter
@Setter
public class DefaultCaseStatement extends Statement<ScriptLanguageParser.StmtListContext> {
    protected Statements body;

    public DefaultCaseStatement() {
        this.body = new Statements();
    }

    public DefaultCaseStatement(Statements body) {
        this.body = body;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public DefaultCaseStatement copy() {
        DefaultCaseStatement dcs = new DefaultCaseStatement(body.copy());
        dcs.setRuleContext(this.ruleContext);
        return dcs;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        DefaultCaseStatement that = (DefaultCaseStatement) o;

        return getBody().eq(that.getBody());
    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + getBody().hashCode();
        return result;
    }


    @Override
    public ASTNode[] getChildren() {
        return new ASTNode[]{getBody()};
    }
}



