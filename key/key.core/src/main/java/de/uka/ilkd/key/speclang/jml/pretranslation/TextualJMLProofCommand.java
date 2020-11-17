package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.speclang.njml.JmlParser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * @author Alexander Weigl
 * @version 1 (11/16/20)
 */
public class TextualJMLProofCommand extends TextualJMLConstruct{
    final JmlParser.ProofcommandContext ctx;

    public TextualJMLProofCommand(JmlParser.ProofcommandContext ctx) {
        super(ImmutableSLList.nil(), "command");
        this.ctx = ctx;
    }

    public String getCommand() {
        return ctx.COMMAND().toString().substring(3);
    }
}
