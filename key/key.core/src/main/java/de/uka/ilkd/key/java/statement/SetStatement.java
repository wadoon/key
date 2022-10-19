package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.speclang.njml.JmlParser;
import org.key_project.util.ExtList;

public class SetStatement extends CopyAssignment {
    private JmlParser.Set_statementContext context;

    public SetStatement(ExtList children, JmlParser.Set_statementContext context) {
        super(children);
        this.context = context;
    }

    public JmlParser.Set_statementContext takeParserContext() {
        var context = this.context;
        this.context = null;
        return context;
    }
}
