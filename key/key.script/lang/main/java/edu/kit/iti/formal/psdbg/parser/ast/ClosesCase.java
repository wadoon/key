package edu.kit.iti.formal.psdbg.parser.ast;

import edu.kit.iti.formal.psdbg.parser.Visitor;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * Object representing  a "closes closeScriptCall(): { Commands}" block in a cases
 */
@Data
@NoArgsConstructor
public class ClosesCase extends CaseStatement {
    /**
     * Script that should be executed and shown whether case can be closed
     */
    private Statements closesGuard;

    /**
     * A close subscript() {bodyscript} expression
     *
     * @param closesGuard the script that is exectued in order to determine whether goal would clos. This proof is pruned afterwards
     * @param body        the actual script that is then executed when closesscript was successful and pruned
     */
    public ClosesCase(Statements closesGuard, Statements body) {
        this.body = body;
        this.closesGuard = closesGuard;
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
    public ClosesCase copy() {
        ClosesCase cs = new ClosesCase(closesGuard.copy(), body.copy());
        cs.setRuleContext(this.ruleContext);
        return cs;
    }

    @Override
    public boolean eq(ASTNode o) {
        if (this == o) return true;
        if (!(o instanceof ClosesCase)) return false;
        if (!super.equals(o)) return false;

        ClosesCase that = (ClosesCase) o;

        return getClosesGuard() != null ? getClosesGuard().eq(that.getClosesGuard()) : that.getClosesGuard() == null;
    }


    @Override
    public ASTNode[] getChildren() {
        return new ASTNode[]{getClosesGuard(), getBody()};
    }
}
