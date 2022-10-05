package javacc;

import javacc.Token;
import javacc.TokenManager;
import org.fife.ui.rsyntaxtextarea.TokenImpl;
import org.fife.ui.rsyntaxtextarea.TokenMakerBase;

import javax.swing.text.Segment;
import java.util.LinkedList;
import java.util.List;

public class JavaCCTokenMaker extends TokenMakerBase {

    private JavaCCLexerFactory factory;

    public JavaCCTokenMaker(JavaCCLexerFactory factory) {
        this.factory = factory;
    }

    private org.fife.ui.rsyntaxtextarea.Token toList(Segment text, int startOffset,
                                                     List<Token> javaccTokens, PositionStream stream) {
        if (javaccTokens.isEmpty()) {
            return null;
        } else {
            javacc.Token token = javaccTokens.get(0);
            // Token start index in text?
            int startIndex = stream.getPos(token.beginLine, token.beginColumn);
            TokenImpl rstaToken = new TokenImpl(text, text.offset + startIndex,
                    text.offset + startIndex + token.image.length() - 1,
                    startOffset + startIndex, token.kind, 0);
            rstaToken.setNextToken(toList(text, startOffset, javaccTokens.subList(1, javaccTokens.size()), stream));
            return rstaToken;
        }
    }

    @Override
    public org.fife.ui.rsyntaxtextarea.Token getTokenList(Segment text, int initialTokenType, int startOffset) {
        if (text == null) {
            throw new IllegalArgumentException();
        }
        // init TokenManager
        PositionStream stream = factory.createStream(text.toString());
        TokenManager manager = factory.create(stream);
        List<Token> tokens = new LinkedList<>();
        Token currentToken = manager.getNextToken();
        while (currentToken.kind != factory.eof()) {
            tokens.add(currentToken);
            // TODO program becomes unusable if a TokenMgrException is thrown here
            currentToken = manager.getNextToken();
        }
        if (tokens.isEmpty()) {
            tokens.add(factory.eofToken());
        }
        return toList(text, startOffset, tokens, stream);
    }

}