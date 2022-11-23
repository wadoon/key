package de.uka.ilkd.key.nparser.format;

import de.uka.ilkd.key.nparser.KeYLexer;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.util.Arrays;

/**
 * Adds spaces after terminals, in comma separated lists and breaks after semicolons
 */
public class ExpressionVisitor extends KeYParserBaseVisitor<Void> {
    private static final int[] OPERATORS = {
            KeYLexer.LESS,
            KeYLexer.LESSEQUAL,
            KeYLexer.GREATER,
            KeYLexer.GREATEREQUAL,
            KeYLexer.EQUALS,
            KeYLexer.NOT_EQUALS,
            KeYLexer.IMP,
            KeYLexer.SEQARROW,
            KeYLexer.NOT_EQUALS,
            KeYLexer.AND,
            KeYLexer.OR,
            KeYLexer.PARALLEL,
            KeYLexer.EXP,
            KeYLexer.PERCENT,
            KeYLexer.STAR,
            KeYLexer.MINUS,
            KeYLexer.PLUS,
            KeYLexer.RGUILLEMETS,
            KeYLexer.EQV,
            KeYLexer.ASSIGN,
    };

    private final CommonTokenStream ts;
    private final Output output;

    public ExpressionVisitor(CommonTokenStream ts, Output output) {
        this.ts = ts;
        this.output = output;
    }

    @Override
    public Void visitTerminal(TerminalNode node) {
        var token = node.getSymbol().getType();

        boolean isLBrace = token == KeYLexer.LBRACE || token == KeYLexer.LPAREN || token == KeYLexer.LBRACKET;
        if (token == KeYLexer.RBRACE || token == KeYLexer.RPAREN || token == KeYLexer.RBRACKET) {
            output.noSpaceBeforeNext();
            output.exitIndent();
        }

        var isOperator = Arrays.stream(OPERATORS).anyMatch(v -> v == token);
        var isUnaryMinus = token == KeYLexer.MINUS &&
                node.getParent() instanceof KeYParser.Unary_minus_termContext;
        // Unary minus has a "soft" leading space, we allow it if the token before wants it but don't require it
        if ((isOperator && !isUnaryMinus) || token == KeYLexer.AVOID) {
            output.spaceBeforeNext();
        }

        String str = node.getSymbol().getText();
        output.token(str);

        if (!isLBrace && ((isOperator && !isUnaryMinus) ||
                token == KeYLexer.COMMA ||
                token == KeYLexer.SUBST ||
                token == KeYLexer.AVOID ||
                token == KeYLexer.EXISTS ||
                token == KeYLexer.FORALL ||
                token == KeYLexer.SEMI)
        ) {
            output.spaceBeforeNext();
        }

        if (isLBrace) {
            output.enterIndent();
        }

        KeYFileFormatter.processHiddenTokensAfterCurrent(node.getSymbol(), ts, output);
        return super.visitTerminal(node);
    }

    @Override
    public Void visitIfThenElseTerm(KeYParser.IfThenElseTermContext ctx) {
        for (int i = 0; i < ctx.getChildCount(); i++) {
            var child = ctx.getChild(i);
            if (child instanceof TerminalNode) {
                var token = ((TerminalNode) child).getSymbol().getType();
                if (token == KeYParser.THEN) {
                    output.enterIndent();
                }

                if (token == KeYParser.THEN || token == KeYParser.ELSE) {
                    output.spaceBeforeNext();
                }
            }
            visit(child);
        }
        output.exitIndent();
        return null;
    }
}
