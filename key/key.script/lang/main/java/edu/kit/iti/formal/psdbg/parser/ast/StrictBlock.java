package edu.kit.iti.formal.psdbg.parser.ast;

import edu.kit.iti.formal.psdbg.parser.Visitor;

public class StrictBlock extends UnconditionalBlock {
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public StrictBlock copy() {
        StrictBlock sb = new StrictBlock();
        sb.body = body.copy();
        sb.ruleContext = ruleContext;
        return sb;
    }
}
