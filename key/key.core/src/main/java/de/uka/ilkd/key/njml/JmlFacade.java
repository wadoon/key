package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.speclang.PositionedString;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.Pair;
import org.key_project.util.collection.ImmutableSet;

/**
 * @author Alexander Weigl
 * @version 1 (5/10/20)
 */
public class JmlFacade {
    public static JmlLexer createLexer(CharStream strea) {
        JmlLexer lexer = new JmlLexer(strea);
        return lexer;
    }

    public static JmlLexer createLexer(PositionedString ps) {
        CharStream result = CharStreams.fromString(ps.text, ps.fileName);
        JmlLexer lexer = createLexer(result);
        lexer._tokenStartCharPositionInLine = ps.pos.getColumn();
        lexer._tokenStartLine = 1 + ps.pos.getLine();
        return lexer;
    }

    public static JmlLexer createLexer(String expr) {
        return createLexer(CharStreams.fromString(expr));
    }

    public static JmlParser.ExpressionContext parseExpr(PositionedString expr) {
        final JmlLexer lexer = createLexer(expr);
        lexer._mode = JmlLexer.expr;
        JmlParser parser = createParser(lexer);
        return parser.expressionEOF().expression();
    }

    public static JmlParser.ExpressionContext parseExpr(String expr) {
        final JmlLexer lexer = createLexer(expr);
        lexer._mode = JmlLexer.expr;
        JmlParser parser = createParser(lexer);
        return parser.expressionEOF().expression();
    }

    static JmlParser createParser(JmlLexer lexer) {
        return new JmlParser(new CommonTokenStream(lexer));
    }

    public static ParserRuleContext parseTop(PositionedString expr) {
        JmlParser p = createParser(createLexer(expr));
        return p.classlevel_comment();
    }

    public static ParserRuleContext parseClause(String s) {
        JmlParser p = createParser(createLexer(s));
        return p.clause();//TODO EOF
    }

    public static ParserRuleContext parseClause(ImmutableSet<PositionedString> nonNullPositionedString) {
        StringBuilder s = new StringBuilder();
        for (PositionedString string : nonNullPositionedString) {
            s.append(string).append("\n");
        }
        return parseClause(s.toString());
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
