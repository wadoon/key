package de.uka.ilkd.key.njml;

import com.google.common.base.Stopwatch;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.Interval;
import org.jetbrains.annotations.NotNull;
import org.key_project.util.collection.ImmutableList;

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

    public static ParserRuleContext parseExpr(PositionedString expr) {
        return getExpressionContext(createLexer(expr));
    }

    public static ParserRuleContext parseExpr(String expr) {
        return getExpressionContext(createLexer(expr));
    }

    private static ParserRuleContext getExpressionContext(JmlLexer lexer) {
        lexer._mode = JmlLexer.expr;
        JmlParser parser = createParser(lexer);
        JmlParser.ExpressionEOFContext ctx = parser.expressionEOF();
        ParserRuleContext c;
        if (ctx.expression() != null) {
            c = ctx.expression();
        } else {
            c = ctx.storeref();
        }
        if (c == null)
            throw new NullPointerException();
        return c;
    }

    static JmlParser createParser(JmlLexer lexer) {
        JmlParser p = new JmlParser(new CommonTokenStream(lexer));
        p.addErrorListener(new BaseErrorListener() {
            @Override
            public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, int charPositionInLine, String msg, RecognitionException e) {
                Token t = (Token) offendingSymbol;
                System.err.println(t.getTokenSource().getInputStream().getText(Interval.of(0, 10000)));
                throw new RuntimeException("line " + line + ":" + charPositionInLine + " " + msg);
            }
        });
        return p;
    }

    public static ParserRuleContext parseTop(PositionedString expr) {
        JmlParser p = createParser(createLexer(expr));
        Stopwatch sw = Stopwatch.createStarted();
        JmlParser.Classlevel_commentsContext ctx = p.classlevel_comments();
        //System.out.println("JmlFacade.parseTop: " + sw.toString());
        return ctx;
    }

    public static ParserRuleContext parseClause(String s) {
        JmlParser p = createParser(createLexer(s));
        return p.clauseEOF().clause();
    }

    static ImmutableList<TextualJMLConstruct> parseClasslevel(JmlLexer lexer) {
        @NotNull JmlParser p = createParser(lexer);
        Stopwatch sw = Stopwatch.createStarted();
        JmlParser.Classlevel_commentsContext ctx = p.classlevel_comments();
        TextualTranslator translator = new TextualTranslator();
        ctx.accept(translator);
        //System.out.println("JmlFacade.parseClasslevel: " + sw);
        return translator.constructs;
    }

    public static ImmutableList<TextualJMLConstruct> parseClasslevel(PositionedString positionedString) {
        return parseClasslevel(createLexer(positionedString));
    }

    public static ImmutableList<TextualJMLConstruct> parseClasslevel(String string) {
        return parseClasslevel(createLexer(string));
    }

    public static ImmutableList<TextualJMLConstruct> parseMethodlevel(PositionedString positionedString) {
        return parseMethodlevel(createLexer(positionedString));
    }

    private static ImmutableList<TextualJMLConstruct> parseMethodlevel(JmlLexer lexer) {
        @NotNull JmlParser p = createParser(lexer);
        Stopwatch sw = Stopwatch.createStarted();
        JmlParser.Methodlevel_commentContext ctx = p.methodlevel_comment();
        TextualTranslator translator = new TextualTranslator();
        ctx.accept(translator);
        //System.out.println("JmlFacade.parseMethodlevel: " + sw);
        return translator.constructs;
    }

    public static void TODO() {
        throw new IllegalStateException("to be implemented");
    }
}

