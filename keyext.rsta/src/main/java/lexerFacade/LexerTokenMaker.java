package lexerFacade;

import lexerFacade.Lexer;
import lexerFactories.LanguageSupportFactory;
import org.fife.ui.rsyntaxtextarea.Token;
import org.fife.ui.rsyntaxtextarea.TokenImpl;
import org.fife.ui.rsyntaxtextarea.TokenMakerBase;
import org.fife.ui.rsyntaxtextarea.TokenTypes;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import javax.swing.text.Segment;
import java.util.ArrayList;
import java.util.List;

/**
 * A {@link org.fife.ui.rsyntaxtextarea.TokenMaker} for implementations of {@link Lexer}
 * created by a {@link LanguageSupportFactory}.
 *
 * @author Alexander Weigl, Alicia Appelhagen
 */
public class LexerTokenMaker extends TokenMakerBase {

    private static final Logger LOGGER = LoggerFactory.getLogger(LexerTokenMaker.class);

    /**
     * Creates {@link Lexer} objects for a given input.
     */
    private LanguageSupportFactory factory;

    public LexerTokenMaker(LanguageSupportFactory factory) {
        this.factory = factory;
    }

    @Override
    public Token getTokenList(Segment text, int initialTokenType, int startOffset) {
        if (text == null) {
            throw new IllegalArgumentException();
        }
        resetTokenList();

        // Create a lexer for the given text segment.
        String textSegment = text.toString();
        Lexer lexer = factory.create(textSegment);

        // initialTokenType contains the mode stack of the lexer
        int initTokType = initialTokenType;
        int mode = initTokType & 0xF; // TODO currently assuming exactly 4 bits for lexer mode, change that?
        lexer.setMode(mode);
        initTokType = initTokType >> 4;
        while (initTokType > 0) {
            mode = initTokType & 0xF;
            lexer.pushMode(mode);
            initTokType = initTokType >> 4;
        }

        List<TokenFacade> tokens = new ArrayList<>();
        List<Integer> modeStack = new ArrayList<>();
        TokenFacade cur = lexer.nextToken();
        modeStack.add(lexer.getMode());
        tokens.add(cur);
        // TODO
        while (!lexer.finished()) {
            System.out.format("%25s %-25s%n", cur.text, factory.allTokenTypeNames().get(cur.tokenType));
            int m = lexer.getMode();
            cur = lexer.nextToken();
            modeStack.add(m);
            tokens.add(cur);
        }

        /*if (cur.tokenType == lexer.eofTokenType() && cur.stopIndex - cur.startIndex > 0) {
            // TODO what exactly is happening here
            changeType(lexer, cur);
            if (cur.tokenType != org.antlr.v4.runtime.Token.EOF) {
                modeStack.add(lexer.getMode());
                tokens.add(cur);
            }
        }*/

        if (tokens.size() == 0) {
            // If the lexer did not lex anything, just pack the whole text into one token.
            currentToken = new TokenImpl(text,
                    text.offset,
                    text.offset,
                    startOffset, 0, 0);

            TokenImpl modeToken = new TokenImpl() {
                @Override
                public boolean isPaintable() {
                    return false;
                }
            };
            modeToken.text = null;
            modeToken.setOffset(-1);
            modeToken.setNextToken(null);
            // mode stack hasn't changed
            modeToken.setType(initialTokenType);
            currentToken.setNextToken(modeToken);
            return currentToken;
        } else {
            mode = 0;
            // skip last artificial '\n' token
            // TODO ?
            for (int i = 0; i < tokens.size(); i++) {
                TokenFacade token = tokens.get(i);
                mode = modeStack.get(i);
                int newType = rewriteTokenType(token.tokenType);
                int start = token.startIndex;
                TokenImpl newToken = new TokenImpl(text,
                        text.offset + start,
                        text.offset + start + token.text.length() - 1,
                        startOffset + start, newType, 0);
                // TODO ?
                newToken.setLanguageIndex(mode);
                if (firstToken == null) {
                    firstToken = newToken;
                } else {
                    assert (currentToken != null);
                    currentToken.setNextToken(newToken);
                }
                currentToken = newToken;
            }

            // encode current mode stack in token type
            // TODO only 32 bits for the mode stack (aka 8 modes in this encoding?)
            int modeTokenType = 0xF & simulateNewLine(lexer);
            while (lexer.getModeStack().size() > 0) {
                modeTokenType = (modeTokenType << 4) | (0xF & lexer.popMode());
            }

            TokenImpl modeToken = new TokenImpl() {
                @Override
                public boolean isPaintable() {
                    return false;
                }
            };
            modeToken.text = null;
            modeToken.setOffset(-1);
            modeToken.setNextToken(null);
            modeToken.setType(modeTokenType);
            currentToken.setNextToken(modeToken);
        }
        return firstToken;
    }

    // TODO use types that are not static variables in TokenTypes here
    protected int rewriteTokenType(int tokenType) {
        return tokenType;
    }

    // TODO ?
    protected void changeType(Lexer lexer, TokenFacade cur) {
    }

    // TODO ?
    protected int simulateNewLine(Lexer lexer) {
        return lexer.getMode();
    }

}
