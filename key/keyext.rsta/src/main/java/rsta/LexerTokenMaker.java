package rsta;

import org.fife.ui.rsyntaxtextarea.Token;
import org.fife.ui.rsyntaxtextarea.TokenImpl;
import org.fife.ui.rsyntaxtextarea.TokenMakerBase;

import javax.annotation.Nullable;
import javax.swing.text.Segment;
import java.util.ArrayList;
import java.util.List;

public class LexerTokenMaker extends TokenMakerBase {

    private LanguageSupportFactory factory;

    public LexerTokenMaker(LanguageSupportFactory factory) {
        this.factory = factory;
    }

    @Nullable
    private Token toRSTAToken(Segment text, int startOffset,
                         List<Integer> startIndices, List<Integer> tokenTypes, List<String> tokenTexts) {
        assert(startIndices.size() == tokenTypes.size() && startIndices.size() == tokenTexts.size());
        if (startIndices.isEmpty()) {
            return null;
        } else {
            int currentIndex = startIndices.get(0);
            int currentType = tokenTypes.get(0);
            String currentText = tokenTexts.get(0);
            TokenImpl rstaToken = new TokenImpl(text, text.offset + currentIndex,
                    text.offset + currentIndex + currentText.length() - 1,
                    startOffset + currentIndex, currentType, 0);
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
        Lexer lexer = factory.create(text.toString());
        List<Integer> startIndices = new ArrayList<>();
        List<Integer> tokenTypes = new ArrayList<>();
        List<String> tokenTexts = new ArrayList<>();
        while (!lexer.finished()) {
            lexer.step();
            startIndices.add(lexer.lastConsumedTokenStartIndex());
            tokenTypes.add(lexer.lastConsumedTokenType());
            tokenTexts.add(lexer.lastConsumedTokenText());
        }
        if (startIndices.isEmpty()) {
            startIndices.add(0);
            tokenTypes.add(lexer.eofTokenType());
            tokenTexts.add(lexer.eofTokenText());
        }
        return toRSTAToken(text, startOffset, startIndices, tokenTypes, tokenTexts);
    }

}
