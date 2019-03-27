package edu.kit.iti.formal.psdbg.parser.ast;

import edu.kit.iti.formal.psdbg.parser.Visitor;

public class RelaxBlock extends UnconditionalBlock {
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public RelaxBlock copy() {
        RelaxBlock sb = new RelaxBlock();
        sb.body = body.copy();
        sb.ruleContext = ruleContext;
        return sb;
    }
}
