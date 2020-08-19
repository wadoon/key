package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.util.Pair;
import org.antlr.v4.runtime.ParserRuleContext;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class LabeledParserRuleContext extends Pair<ParserRuleContext, TermLabel> {
    public LabeledParserRuleContext(ParserRuleContext first, TermLabel second) {
        super(first, second);
        if(first==null) throw new IllegalArgumentException("ParserRuleContext is null");
    }

    public LabeledParserRuleContext(ParserRuleContext first) {
        super(first, null);
    }

}
