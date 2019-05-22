package org.key_project.editor.java;

import lombok.val;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.Recognizer;
import org.fife.ui.rsyntaxtextarea.Token;
import org.fife.ui.rsyntaxtextarea.TokenImpl;
import org.fife.ui.rsyntaxtextarea.TokenMakerBase;

import javax.swing.text.Segment;
import java.util.ArrayList;
import java.util.List;

public abstract class Antlr4TokenMakerFactory extends TokenMakerBase {
    /* @see <https://tomassetti.me/how-to-create-an-editor-with-syntax-highlighting-dsl/> */
    @Override
    public Token getTokenList(Segment text, int initialTokenType, int startOffset) {
        resetTokenList();
        if (text == null) {
            throw new IllegalArgumentException();
        }

        Lexer lexer = createLexer(text.toString());
        List<org.antlr.v4.runtime.Token> tokens = new ArrayList<>();
        org.antlr.v4.runtime.Token cur = lexer.nextToken();
        while (cur.getType() != Recognizer.EOF) {
            System.out.format("%25s %-25s%n", cur.getText(), lexer.getVocabulary().getSymbolicName(cur.getType()));

            tokens.add(cur);
            cur = lexer.nextToken();
        }


        if (tokens.isEmpty()) {
            addNullToken();
        } else {
            TokenImpl lastToken = null;
            for (org.antlr.v4.runtime.Token token : tokens) {
                int newType = rewriteTokenType(token.getType());
                int start = token.getStartIndex();
                val t = new TokenImpl(text,
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

