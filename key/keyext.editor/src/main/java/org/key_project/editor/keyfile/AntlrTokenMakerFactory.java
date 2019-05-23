package org.key_project.editor.keyfile;

import org.antlr.runtime.Lexer;
import org.fife.ui.rsyntaxtextarea.Token;
import org.fife.ui.rsyntaxtextarea.TokenImpl;
import org.fife.ui.rsyntaxtextarea.TokenMakerBase;

import javax.swing.text.Segment;
import java.util.ArrayList;
import java.util.List;

public abstract class AntlrTokenMakerFactory extends TokenMakerBase {
    /* @see <https://tomassetti.me/how-to-create-an-editor-with-syntax-highlighting-dsl/> */
    @Override
    public Token getTokenList(Segment text, int initialTokenType, int startOffset) {
        resetTokenList();
        if (text == null) {
            throw new IllegalArgumentException();
        }

        Lexer lexer = createLexer(text.toString());
        List<org.antlr.runtime.Token> tokens = new ArrayList<>();
        org.antlr.runtime.Token cur = lexer.nextToken();
        while (cur.getType() != -1) { //EOF
            //System.out.format("%25s %-25s%n", cur.getText(), lexer.getVocabulary().getSymbolicName(cur.getType()));
            tokens.add(cur);
            cur = lexer.nextToken();
        }


        if (tokens.isEmpty()) {
            addNullToken();
        } else {
            TokenImpl lastToken = null;
            for (org.antlr.runtime.Token token : tokens) {
                int newType = rewriteTokenType(token.getType());
                int start = token.getCharPositionInLine(); //.getStartIndex();
                TokenImpl t = new TokenImpl(text,
                        text.offset + start,
                        text.offset + start + token.getText().length() - 1,
                        startOffset + start, newType, 0);
                if (firstToken == null) {
                    firstToken = t;
                } else {
                    assert lastToken != null;
                    lastToken.setNextToken(t);
                }
                lastToken = t;
            }
        }
        return firstToken;
    }

    protected abstract int rewriteTokenType(int antlrType);

    protected abstract Lexer createLexer(String toString);
}

