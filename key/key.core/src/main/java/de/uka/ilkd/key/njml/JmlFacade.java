package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.Pair;
import org.key_project.util.collection.ImmutableList;

/**
 * @author Alexander Weigl
 * @version 1 (5/10/20)
 */
public class JmlFacade {
    public static CharStream createANTLRStringStream(PositionedString ps) {
        CodePointCharStream result = CharStreams.fromString(ps.text, ps.fileName);
        //result.setCharPositionInLine(ps.pos.getColumn());
        //result.setLine(ps.pos.getLine() + 1);
        return result;
    }

    public static JmlLexer createLexer(PositionedString ps) {
        CharStream result = CharStreams.fromString(ps.text, ps.fileName);
        JmlLexer lexer = new JmlLexer(result);
        lexer._tokenStartCharPositionInLine = ps.pos.getColumn();
        lexer._tokenStartLine = 1 + ps.pos.getLine();
        return lexer;
    }

    public ImmutableList<TextualJMLConstruct> parseClasslevelComment() throws SLTranslationException {
        try {
            return classlevel_comment();
        } catch(RecognitionException e) {
            throw excManager.convertException(getErrorMessage(e, KeYJMLPreLexerTokens.getTokennames()), e);
        }
    }


    public ImmutableList<TextualJMLConstruct> parseMethodlevelComment()
            throws SLTranslationException {
        try {
            return methodlevel_comment();
        } catch(RecognitionException e) {
            throw excManager.convertException(getErrorMessage(e, KeYJMLPreLexerTokens.getTokennames()), e);
        }
    }


    private static class OffsetFactory extends CommonTokenFactory {
        int lineOffset;
        int charPositionInLineOffset;
        int charOffset;

        public OffsetFactory(boolean copyText) {
            super(copyText);
        }

        public OffsetFactory() {
            super();
        }

        @Override
        public CommonToken create(Pair<TokenSource, CharStream> source, int type, String text, int channel, int start, int stop, int line, int charPositionInLine) {
            CommonToken ct = super.create(source, type, text, channel, start, stop, line, charPositionInLine);
            return ct;
        }

        @Override
        public CommonToken create(int type, String text) {
            CommonToken ct = super.create(type, text);
            applyOffset(ct);
            return ct;

        }

        private void applyOffset(CommonToken ct) {
            ct.setCharPositionInLine(ct.getCharPositionInLine() + charPositionInLineOffset);
            ct.setLine(ct.getLine() + lineOffset);
            ct.setStartIndex(ct.getStartIndex() + charOffset);
            ct.setStopIndex(ct.getStopIndex() + charOffset);

        }
    }
}
