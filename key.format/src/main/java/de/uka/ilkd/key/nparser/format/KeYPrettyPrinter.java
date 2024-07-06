package de.uka.ilkd.key.nparser.format;

import de.uka.ilkd.key.nparser.KeYLexer;
import de.uka.ilkd.key.nparser.ParsingFacade;
import org.antlr.v4.runtime.Token;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.List;

public class KeYPrettyPrinter {

    private static final int INDENT_STEP = 4;

    public static void main(String[] args) throws IOException {
        Path testDir = Paths.get("/home/wolfram/Desktop/tmp");
        Files.list(testDir.resolve("rules")).forEach(p -> {
            try {
                Files.writeString(testDir.resolve("testoutput").resolve(p.getFileName()),
                    prettyPrint(p));
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        });
    }

    private static StringBuilder prettyPrint(Path input) throws IOException {
        StringBuilder builder = new StringBuilder();
        KeYLexer lexer = ParsingFacade.createLexer(input);
        List<? extends Token> tokens = lexer.getAllTokens();
        int indent = 0;
        int cur = 0;
        for (Token token : tokens) {
            String text = token.getText();
            switch (token.getType()) {
            case KeYLexer.LPAREN:
            case KeYLexer.LBRACE:
                indent++;
                break;
            case KeYLexer.RPAREN:
            case KeYLexer.RBRACE:
                if (indent == 0) {
                    System.err.printf("Mmmh. Mismatched parentheses/braces at %d/%d.",
                        token.getLine(), token.getCharPositionInLine());
                } else {
                    indent--;
                }
                break;
            case KeYLexer.WS:
                int nls = countNLs(text);
                if (nls > 0) {
                    int i = indent;
                    if (cur < tokens.size() - 1) {
                        int nextTy = tokens.get(cur + 1).getType();
                        if (nextTy == KeYLexer.RPAREN || nextTy == KeYLexer.RBRACE)
                            i--;
                    }
                    text = multi(nls, "\n") + multi(INDENT_STEP * i, " ");
                }
                break;
            // case KeYLexer.SL_COMMENT: // TODO: other comment types
            // text = processIndentationInSLComment(token, indent);
            }
            builder.append(text);
            cur++;
        }
        return builder;
    }

    private static String processIndentationInSLComment(Token t, int indent) {
        return t.getText().trim() + '\n' + multi(INDENT_STEP * indent, " ");
    }

    private static int countNLs(String text) {
        return (int) text.chars().filter(x -> x == '\n').count();
    }

    private static String multi(int count, String s) {
        return String.join("", Collections.nCopies(count, s));
    }
}
