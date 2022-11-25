package lexerFactories;

import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import recoder.java.expression.operator.LogicalAnd;
import rsta.LanguageSupportFactory;
import rsta.Lexer;

import javax.annotation.Nullable;
import java.util.*;

public class VariousGrammarsSyntaxSchemeFactory implements LanguageSupportFactory {

    private final LexerDelegationMap lexerDelegationMap;
    private final List<LanguageSupportFactory> lexerOrder;
    private Map<Integer, String> allTokenTypeNames = new HashMap<>();

    public VariousGrammarsSyntaxSchemeFactory(List<LanguageSupportFactory> lexerOrder, LexerDelegationMap lexerDelegationMap) {
        // TODO create this map via json?
        this.lexerDelegationMap = lexerDelegationMap;
        this.lexerOrder = new ArrayList<>(lexerOrder);
        for (LanguageSupportFactory factory: lexerOrder) {
            Map<Integer, String> map = factory.allTokenTypeNames();
            if (map == null) {
                continue;
            }
            for (Map.Entry<Integer, String> mapping : map.entrySet()) {
                // TODO SyntaxScheme definition has problems if different tokens have the same name here
                allTokenTypeNames.put(evaluateTokenType(factory, mapping.getKey()), mapping.getValue());
            }
        }
    }

    // TODO make this the EOF token of the first lexer/factory
    private final int EOF = 0;

    private int evaluateTokenType(LanguageSupportFactory factory, int tokenType) {
        // TODO make more memory (and runtime) efficient
        OptionalInt maxTokenAmount = lexerOrder.stream()
                .mapToInt(l -> l.allTokenTypeNames() == null ? 0 : l.allTokenTypeNames().entrySet().size())
                .max();
        int maxTokens = maxTokenAmount.isEmpty() ? 0 : maxTokenAmount.getAsInt();
        if (tokenType > maxTokens) {
            return EOF;
        }
        for (int index = 0; index < lexerOrder.size(); index++) {
            // Make sure the first lexer gets its tokens mapped to their original value to have the EOF tokens match.
            if (lexerOrder.get(index).equals(factory)) {
                return index*maxTokens+tokenType;
            }
        }
        return EOF;
    }

    @Nullable
    @Override
    public Lexer create(String toLex) {
        return new Lexer() {


            LanguageSupportFactory currentFactory = lexerOrder.get(0);
            Lexer currentLexer = currentFactory.create(toLex);
            Lexer oldLexer = currentLexer;
            String lastConsumedTokenText;
            int lastConsumedTokenType;

            int lastConsumedStartIndex = 0;

            @Override
            public void step() {
                currentLexer.step();
                String currentLastConsumedText = currentLexer.lastConsumedTokenText();
                int currentLastConsumedType = currentLexer.lastConsumedTokenType();
                /*
                Case 1: The current lexer consumes the token and does not have to delegate it.
                 */
                LanguageSupportFactory newFactory = lexerDelegationMap.getNextLexer(currentFactory, currentLastConsumedType);
                if (newFactory == null) {
                    lastConsumedTokenType = currentLastConsumedType;
                    lastConsumedTokenText = currentLastConsumedText;
                    int currentLastConsumedStartIndex = currentLexer.lastConsumedTokenStartIndex();
                    // current lexer does the next step unless it is finished
                    if (currentLexer.finished()) {
                        currentLexer = oldLexer;
                    }
                    return;
                }
                /*
                Case 2: The current lexer consumes the token and has to delegate it further.
                 */
                oldLexer = currentLexer;
                currentLexer = newFactory.create(currentLastConsumedText);
                step();
            }

            @Override
            public boolean finished() {
                // finished if the first lexer reached EOF
                return currentFactory.equals(lexerOrder.get(0)) && currentLexer.finished();
            }

            @Override
            public String lastConsumedTokenText() {
                return lastConsumedTokenText;
            }

            @Override
            public Integer lastConsumedTokenStartIndex() {
                int currentLastConsumedStartIndex = currentLexer.lastConsumedTokenStartIndex();
                lastConsumedStartIndex = (currentFactory.equals(lexerOrder.get(0)))
                        ? currentLastConsumedStartIndex
                        : currentLastConsumedStartIndex + lastConsumedStartIndex;
                return lastConsumedStartIndex;
            }

            @Override
            public Integer lastConsumedTokenType() {
                return lastConsumedTokenType;
            }

            @Override
            public Integer eofTokenType() {
                // TODO first lexer's eof token
                return 0;
            }

            @Override
            public String eofTokenText() {
                // TODO first lexer's eof token
                return "<EOF>";
            }

        };
    }

    @Override
    public Map<Integer, String> allTokenTypeNames() {
        return allTokenTypeNames;
    }

    @Override
    public SyntaxScheme getSyntaxScheme() {
        return null;
    }

    /**
     * Note that the lexer order in the map may be relevant.
     */
    public static class LexerDelegationMap {

        private final Map<LanguageSupportFactory, Map<Integer, LanguageSupportFactory>> delegationMap;

        public LexerDelegationMap(Map<LanguageSupportFactory, Map<Integer, LanguageSupportFactory>> delegationMap) {
            this.delegationMap = delegationMap;
        }

        @Nullable
        public LanguageSupportFactory getNextLexer(LanguageSupportFactory currentLexer, Integer tokenType) {
            Map<Integer, LanguageSupportFactory> delegationTable = delegationMap.get(currentLexer);
            return delegationTable == null ? null : delegationTable.get(tokenType);
        }

        static int getIndex(LanguageSupportFactory factory, List<LanguageSupportFactory> orderedList) {
            for (int i = 0; i < orderedList.size(); i++) {
                if (orderedList.get(i).equals(factory)) {
                    return i;
                }
            }
            return orderedList.size() + 1;
        }

    }
}
