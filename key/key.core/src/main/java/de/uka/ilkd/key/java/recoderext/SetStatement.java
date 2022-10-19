package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.speclang.njml.JmlParser;
import recoder.java.Expression;
import recoder.java.expression.operator.CopyAssignment;


public class SetStatement extends CopyAssignment {
    private final JmlParser.Set_statementContext context;

    public SetStatement(CopyAssignment proto, JmlParser.Set_statementContext context) {
        super(proto);
        this.context = context;
    }

    @Override
    public SetStatement deepClone() {
        return new SetStatement(this, this.context);
    }

    public JmlParser.Set_statementContext getParserContext() {
        return context;
    }
}
