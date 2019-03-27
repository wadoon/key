package edu.kit.iti.formal.psdbg.parser.ast;

import edu.kit.iti.formal.psdbg.parser.Visitor;

public class WhileStatement extends ConditionalBlock {
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public WhileStatement copy() {
        WhileStatement ws = new WhileStatement();
        ws.ruleContext = ruleContext;
        ws.body = body.copy();
        ws.condition = condition.copy();
        return ws;
    }
}
