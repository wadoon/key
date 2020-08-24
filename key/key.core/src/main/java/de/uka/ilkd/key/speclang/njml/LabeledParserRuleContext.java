package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.util.Pair;
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * This class maps a {@link ParserRuleContext} to a {@link TermLabel}.
 */
public class LabeledParserRuleContext extends Pair<ParserRuleContext, TermLabel> {
    public LabeledParserRuleContext(ParserRuleContext first, TermLabel second) {
        super(first, second);
        if(first==null) throw new IllegalArgumentException("ParserRuleContext is null");
    }

    public LabeledParserRuleContext(ParserRuleContext first) {
        super(first, null);
    }
}
