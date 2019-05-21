package org.key_project.editor.keyfile;

import de.uka.ilkd.key.parser.KeYLexer;
import org.antlr.runtime.Lexer;
import org.fife.ui.rsyntaxtextarea.Token;
import org.fife.ui.rsyntaxtextarea.TokenMakerBase;

import javax.swing.text.Segment;
import java.util.ArrayList;
import java.util.List;

public abstract class AntlrTokenMakerFactory extends TokenMakerBase {
    /**
     * @param text
     * @param initialTokenType
     * @param startOffset
     * @return
     * @see <https://tomassetti.me/how-to-create-an-editor-with-syntax-highlighting-dsl/>
     */
    @Override
    public Token getTokenList(Segment text, int initialTokenType, int startOffset) {
        resetTokenList();
        if (text == null || text.count == 0) {
            throw new IllegalArgumentException();
        }

        Lexer lexer = createLexer(text.toString());
        List<org.antlr.runtime.Token> tokens = new ArrayList<>();
        org.antlr.runtime.Token cur = lexer.nextToken();
        while (cur.getType() != KeYLexer.EOF) {
            tokens.add(cur);
            cur = lexer.nextToken();
        }

        if (tokens.isEmpty()) {
            addNullToken();
        } else {
            for (org.antlr.runtime.Token token : tokens) {
                int startIndex = token.getCharPositionInLine(); // token.getStartIndex() would be better
                addToken(text,
                        startIndex, startIndex + token.getText().length() - 1,
                        rewriteTokenType(token.getType()), text.offset);
            }
        }
        return firstToken;
    }

    protected abstract int rewriteTokenType(int antlrType);

    protected abstract Lexer createLexer(String toString);
}

