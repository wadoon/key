package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.jetbrains.annotations.NotNull;
import org.key_project.util.collection.ImmutableList;

/**
 * @author Alexander Weigl
 * @version 1 (7/1/20)
 */
public class JmlParsingFacade {
    public static ImmutableList<TextualJMLConstruct> parseClasslevel(String ms) {
        return parseClasslevel(CharStreams.fromString(ms));
    }

    private static ImmutableList<TextualJMLConstruct> parseClasslevel(CharStream stream) {
        return null;
    }


    @NotNull
    public JmlParser createParser(@NotNull CharStream stream) {
        JmlLexer lexer = createLexer(stream);
        JmlParser p = new JmlParser(new CommonTokenStream(lexer));
        return p;
    }

    @NotNull
    private JmlLexer createLexer(CharStream stream) {
        return new JmlLexer(stream);
    }


}
