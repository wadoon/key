package de.uka.ilkd.key.nparser.format;

import de.uka.ilkd.key.nparser.KeYLexer;
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

        var isBinary = Arrays.stream(OPERATORS).anyMatch(v -> v == token);

        if (token == KeYLexer.LPAREN) {
            output.enterIndent();
        } else if (token == KeYLexer.RPAREN) {
            output.exitIndent();
        }

        if (isBinary || token == KeYLexer.AVOID) {
            output.spaceBeforeNext();
        }

        String str = node.getSymbol().getText();
        output.token(str);

        if (isBinary ||
                token == KeYLexer.COMMA ||
                token == KeYLexer.SUBST ||
                token == KeYLexer.AVOID ||
                token == KeYLexer.EXISTS ||
                token == KeYLexer.FORALL
        ) {
            output.spaceBeforeNext();
        }

        KeYFileFormatter.processHiddenTokensAfterCurrent(node.getSymbol(), ts, output);
        return super.visitTerminal(node);
    }
}
