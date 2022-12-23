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

public class LexerTokenMaker extends TokenMakerBase {

    private static final Logger LOGGER = LoggerFactory.getLogger(LexerTokenMaker.class);

    /**
     * Improve performance for multiple getTokenList calls with the same input.
     */
    private String cachedText;
    private List<Integer> cachedTypes;
    private List<Integer> cachedIndices;
    private List<String> cachedImages;

    private LanguageSupportFactory factory;

    public LexerTokenMaker(LanguageSupportFactory factory) {
        this.factory = factory;
    }

    @Nullable
    private static Token toRSTAToken(Segment text, int startOffset,
                         List<Integer> startIndices, List<Integer> tokenTypes, List<String> tokenTexts) {
        assert(startIndices.size() == tokenTypes.size() && startIndices.size() == tokenTexts.size());
        if (startIndices.isEmpty()) {
            return null;
        } else {
            int currentIndex = startIndices.get(0);
            int currentType = tokenTypes.get(0);
            if (currentType == TokenTypes.SEPARATOR) {
                LOGGER.warn(currentType  + " equals the static separator constant, help");
            }
            String currentText = tokenTexts.get(0);
            int currentStopIndex = Math.min(currentIndex + currentText.length(), startOffset + text.count)-1;
            if (currentStopIndex < startOffset) {
                return toRSTAToken(text, startOffset,
                        startIndices.subList(1, startIndices.size()),
                        tokenTypes.subList(1, tokenTypes.size()),
                        tokenTexts.subList(1, tokenTexts.size()));
            }
            TokenImpl rstaToken = new TokenImpl(text, Math.max(currentIndex, startOffset), currentStopIndex,
                    currentIndex, currentType, 0);
            if (currentStopIndex >= startOffset + text.count - 1) {
                return rstaToken;
            }
            rstaToken.setNextToken(toRSTAToken(text, startOffset,
                    startIndices.subList(1, startIndices.size()),
                    tokenTypes.subList(1, tokenTypes.size()),
                    tokenTexts.subList(1, tokenTexts.size())));
            return rstaToken;
        }
    }

    @Override
    public Token getTokenList(Segment text, int initialTokenType, int startOffset) {
        if (text == null) {
            throw new IllegalArgumentException();
        }
        String completeText = new String(text.array);
        // Lex the complete text to correctly recognize multiline tokens
        // TODO Optimize this towards real line-by-line lexing
        Lexer lexer = factory.create(completeText);
        List<Integer> startIndices = new ArrayList<>();
        List<Integer> tokenTypes = new ArrayList<>();
        List<String> tokenTexts = new ArrayList<>();
        if (text.count == 0 || startOffset != text.offset) {
            return new TokenImpl(text, text.offset, text.offset,
                    startOffset, lexer.eofTokenType(), 0);
        }
        if (completeText.equals(cachedText)) {
            return toRSTAToken(text, startOffset, cachedIndices, cachedTypes, cachedImages);
        }
        int length = 0;
        while (!lexer.finished() && length < completeText.length()) {
            lexer.step();
            startIndices.add(lexer.lastConsumedTokenStartIndex());
            tokenTypes.add(lexer.lastConsumedTokenType());
            tokenTexts.add(lexer.lastConsumedTokenText());
            length += lexer.lastConsumedTokenText().length();
        }
        if (startIndices.isEmpty()) {
            startIndices.add(0);
            tokenTypes.add(lexer.eofTokenType());
            tokenTexts.add("<EOF>");
        }
        cachedImages = tokenTexts;
        cachedIndices = startIndices;
        cachedTypes = tokenTypes;
        cachedText = completeText;
        // Only return the tokens that are actually part of the text segment
        return toRSTAToken(text, startOffset, startIndices, tokenTypes, tokenTexts);
    }

    /*
    @Override
    public Token getTokenList(Segment text, int initialTokenType, int startOffset) {
        if (text == null) {
            throw new IllegalArgumentException();
        }
        if (startRestOfLastLine != null) {
            text = new Segment(text.array,
                    startRestOfLastLine,
                    text.count + text.offset - startRestOfLastLine + 1);
        }
        Lexer lexer = factory.create(text.toString());
        List<Integer> startIndices = new ArrayList<>();
        List<Integer> tokenTypes = new ArrayList<>();
        List<String> tokenTexts = new ArrayList<>();
        int lastUnambiguousOffset = startOffset;
        while (!lexer.finished()) {
            lexer.saveStatusBeforeHitEOF();
            lastUnambiguousOffset += lexer.lastConsumedTokenText().length() + 1;
            lexer.step();
            startIndices.add(lexer.lastConsumedTokenStartIndex());
            tokenTypes.add(lexer.lastConsumedTokenType());
            tokenTexts.add(lexer.lastConsumedTokenText());
        }
        if (lexer.finished()) {
            // end of line was reached, so we save the rest of the text consumed before hitting EOF
            // in order to start the next line with that rest
            startRestOfLastLine = lastUnambiguousOffset;
        }
        if (startIndices.isEmpty()) {
            startIndices.add(0);
            tokenTypes.add(lexer.eofTokenType());
            tokenTexts.add("");
        }
        return toRSTAToken(text, startOffset, startIndices, tokenTypes, tokenTexts);
    }
    */
}
