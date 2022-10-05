package antlr;

import org.antlr.v4.runtime.Lexer;
import org.fife.ui.rsyntaxtextarea.Token;
import org.fife.ui.rsyntaxtextarea.TokenImpl;
import org.fife.ui.rsyntaxtextarea.TokenMakerBase;

import javax.swing.text.Segment;
import java.util.LinkedList;
import java.util.List;

public class ANTLRTokenMaker extends TokenMakerBase {

    private ANTLRLexerFactory factory;

    public ANTLRTokenMaker(ANTLRLexerFactory factory) {
        this.factory = factory;
    }

    private Token toList(Segment text, int startOffset, List<org.antlr.v4.runtime.Token> antlrTokens) {
        if (antlrTokens.isEmpty()) {
            return null;
        } else {
            org.antlr.v4.runtime.Token token = antlrTokens.get(0);
            int startIndex = token.getStartIndex();
            TokenImpl rstaToken = new TokenImpl(text, text.offset + startIndex,
                    text.offset + startIndex + token.getText().length() - 1,
                    startOffset + startIndex, token.getType(), 0);
            rstaToken.setNextToken(toList(text, startOffset, antlrTokens.subList(1, antlrTokens.size())));
            return rstaToken;
        }
    }

    @Override
    public Token getTokenList(Segment text, int initialTokenType, int startOffset) {
        if (text == null) {
            throw new IllegalArgumentException();
        }
        Lexer lexer = factory.create(text.toString());
        List<org.antlr.v4.runtime.Token> tokens = new LinkedList<>();
        while (!lexer._hitEOF) {
            tokens.add(lexer.nextToken());
        }
        return toList(text, startOffset, tokens);
    }

}


