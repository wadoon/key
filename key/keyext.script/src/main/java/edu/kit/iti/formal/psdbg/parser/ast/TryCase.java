package edu.kit.iti.formal.psdbg.parser.ast;

import edu.kit.iti.formal.psdbg.parser.Visitor;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * Object representing  a "try { Commands}" block in a cases
 */
@Data
@NoArgsConstructor
public class TryCase extends CaseStatement {
    public TryCase(Statements body) {
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
    public TryCase copy() {
        TryCase tc = new TryCase(body.copy());
        tc.setRuleContext(this.getRuleContext());
        return tc;
    }


}
