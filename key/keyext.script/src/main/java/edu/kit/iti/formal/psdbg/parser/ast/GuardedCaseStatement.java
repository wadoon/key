package edu.kit.iti.formal.psdbg.parser.ast;

import edu.kit.iti.formal.psdbg.parser.Visitor;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * Created by sarah on 7/17/17.
 */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class GuardedCaseStatement extends CaseStatement {
    private Expression guard;

    public GuardedCaseStatement(Expression guard, Statements body) {
        this.guard = guard;
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
    public GuardedCaseStatement copy() {
        GuardedCaseStatement scs = new GuardedCaseStatement(guard.copy(), body.copy());
        scs.setRuleContext(this.ruleContext);
        return scs;
    }

    @Override
    public boolean eq(ASTNode o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        GuardedCaseStatement that = (GuardedCaseStatement) o;

        return getGuard().eq(that.getGuard());
    }

    @Override
    public ASTNode[] getChildren() {
        return new ASTNode[]{getGuard(), getBody()};
    }
}
