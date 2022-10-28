package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.speclang.njml.JmlParser;
import recoder.java.Expression;
import recoder.java.expression.operator.CopyAssignment;


public class SetStatement extends CopyAssignment {
    /**
     * Parser context of the assignment
     */
    private final JmlParser.Set_statementContext context;

    /**
     * Primary constructor
     * @param proto the copy assignment
     * @param context the context of the assignment
     */
    public SetStatement(CopyAssignment proto, JmlParser.Set_statementContext context) {
        super(proto);
        this.context = context;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public SetStatement deepClone() {
        return new SetStatement(this, this.context);
    }

    /**
     * Gets the contained parser context
     */
    public JmlParser.Set_statementContext getParserContext() {
        return context;
    }
}
