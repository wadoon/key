package edu.kit.iti.formal.psdbg.parser.ast;

import edu.kit.iti.formal.psdbg.parser.ScriptLanguageParser;
import edu.kit.iti.formal.psdbg.parser.Visitor;

public class IfStatement extends ConditionalBlock {
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public Statement<ScriptLanguageParser.ConditionalBlockContext> copy() {
        IfStatement is = new IfStatement();
        is.ruleContext = ruleContext;
        is.body = body.copy();
        is.condition = condition.copy();
        return is;
    }
}
