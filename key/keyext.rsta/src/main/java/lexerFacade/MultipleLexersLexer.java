package lexerFacade;

import bibliothek.util.container.Tuple;
import lexerFactories.ANTLRLanguageSupportFactory;
import lexerFactories.LanguageSupport;
import lexerFactories.LanguageSupportFactory;
import lexerFactories.VariousGrammarsSyntaxSchemeFactory;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.TuningParameters;

import javax.annotation.Nullable;
import java.util.*;

public class MultipleLexersLexer implements Lexer {

    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(MultipleLexersLexer.class);

    /**
     * The String to be lexed.
     */
    private final String toLex;

    /**
     * Stores information for each lexer/lexer factory about where to delegate which token.
     */
    private final LexerDelegationMap lexerDelegationMap;

    private final List<LanguageSupportFactory> lexerFactoryOrder;

    private final int maxTokens;

    /**
     * Temp variables for recursive descent into the responsible lexer.
     */
    private LanguageSupportFactory currentFactory;
    private Lexer currentLexer;

    private Lexer outerLexer;
    private String lastConsumedTokenText;
    private int lastConsumedTokenType;
    private int lastConsumedStartIndex = 0;

    private final Map<LanguageSupportFactory, Map<Integer, Integer>> uniqueTokenTypes = new HashMap<>();

    public MultipleLexersLexer(List<LanguageSupportFactory> lexerFactoryOrder,
                               LexerDelegationMap delegationMap,
                               String toLex) {
        if (lexerFactoryOrder.isEmpty()) {
            throw new IllegalArgumentException(
                    "Cannot create an instance of " + getClass().getName() + " with an empty lexer factory list.");
        }
        this.currentFactory = lexerFactoryOrder.get(0);
        this.currentLexer = currentFactory.create(toLex);
        this.outerLexer = currentLexer;
        this.lexerDelegationMap = delegationMap;
        this.toLex = toLex;
        this.lexerFactoryOrder = new ArrayList<>(lexerFactoryOrder);
        OptionalInt maxTokenAmount = lexerFactoryOrder.stream()
                .mapToInt(l -> l.allTokenTypeNames() == null ? 0 : l.allTokenTypeNames().entrySet().size())
                .max();
        this.maxTokens = maxTokenAmount.isEmpty() ? 0 : maxTokenAmount.getAsInt();
    }

    private int evaluateTokenType(LanguageSupportFactory factory, int tokenType) {
        if (tokenType > maxTokens) {
            return lexerFactoryOrder.get(0).getEOFTokenType();
        }
        /*
        If a unique token type for the given factory and type has already been cached, just return that.
         */
        Map<Integer, Integer> cachedEvaluatedTokenTypesForFactory = uniqueTokenTypes.get(factory);
        if (cachedEvaluatedTokenTypesForFactory != null) {
            Integer evaluatedType = cachedEvaluatedTokenTypesForFactory.get(tokenType);
            if (evaluatedType != null) {
                return evaluatedType;
            }
        }
        /*
        Otherwise, evaluate the unique token type.
         */
        for (int index = 0; index < lexerFactoryOrder.size(); index++) {
            // Make sure the first lexer gets its tokens mapped to their original value to have the EOF tokens match.
            if (lexerFactoryOrder.get(index).equals(factory)) {
                return index*maxTokens+tokenType;
            }
        }
        /*
        If the given factory dies not exist, just return the eof value of the first factory.
         */
        return lexerFactoryOrder.get(0).getEOFTokenType();
    }

    @Override
    public void step() {
        // Let the current lexer consume its next token.
        currentLexer.step();
        // Temporarily store the current lexer's last consumed token.
        String currentLastConsumedText = currentLexer.lastConsumedTokenText();
        int currentLastConsumedType = currentLexer.lastConsumedTokenType();
        /*
        Case 1: The current lexer does not have to delegate its last consumed token.
         */
        LanguageSupportFactory newFactory = lexerDelegationMap.getNextLexer(currentFactory, currentLastConsumedType);
        if (currentFactory.equals(newFactory)) {
            lastConsumedTokenType = evaluateTokenType(currentFactory, currentLastConsumedType);
            lastConsumedTokenText = currentLastConsumedText;
            return;
        }
        /*
        Case 2: The current lexer consumes the token and has to delegate it further.
         */
        Lexer oldLexer = currentLexer;
        LanguageSupportFactory oldFactory = currentFactory;
        currentFactory = newFactory;
        currentLexer = newFactory.create(currentLastConsumedText);
        step();
        // current lexer does the next step unless it is finished
        if (currentLexer.finished()) {
            currentLexer = oldLexer;
            currentFactory = oldFactory;
        }
    }

    @Override
    public boolean finished() {
        // finished if the first lexer reached EOF
        return outerLexer.finished();
    }

    @Override
    public String lastConsumedTokenText() {
        return lastConsumedTokenText;
    }

    @Override
    public Integer lastConsumedTokenStartIndex() {
        int currentLastConsumedStartIndex = currentLexer.lastConsumedTokenStartIndex();
        lastConsumedStartIndex = (currentFactory.equals(lexerFactoryOrder.get(0)))
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

    /**
     * Note that the lexer order in the map may be relevant.
     */
    public static class LexerDelegationMap {

        /**
         * For each factory, this stores which factories each token (denoted by its int type) should be delegated.
         */
        private final Map<LanguageSupportFactory, Map<Integer, LanguageSupportFactory>> delegationMap;

        public LexerDelegationMap(Map<LanguageSupportFactory, Map<String, LanguageSupportFactory>> delegationMapUsingTokenNames) {
            Map<LanguageSupportFactory, Map<Integer, LanguageSupportFactory>> delegationMap = new HashMap<>();
            for (Map.Entry<LanguageSupportFactory, Map<String, LanguageSupportFactory>> entry: delegationMapUsingTokenNames.entrySet()) {
                Map<Integer, LanguageSupportFactory> delegationEntries = new HashMap<>();
                for (Map.Entry<String, LanguageSupportFactory> delEntry: entry.getValue().entrySet()) {
                    Optional<Integer> tokenType = entry.getKey().allTokenTypeNames().entrySet().stream().filter(
                            e -> delEntry.getKey().equals(e.getValue())
                    ).map(Map.Entry::getKey).findFirst();
                    if (tokenType.isEmpty()) {
                        continue;
                    }
                    delegationEntries.put(tokenType.get(), delEntry.getValue());
                }
                delegationMap.put(entry.getKey(), delegationEntries);
            }
            this.delegationMap = delegationMap;
        }

        /**
         * Returns the currentLexer if this delegation map does not contain a delegation value for
         * the given currentFactory and tokenType.
         *
         * @param currentLexer the current factory
         * @param tokenType the token to be delegated
         * @return the factory that the tokenType token was delegated to by currentLexer
         */
        @Nullable
        public LanguageSupportFactory getNextLexer(LanguageSupportFactory currentLexer, Integer tokenType) {
            Map<Integer, LanguageSupportFactory> delegationTable = delegationMap.get(currentLexer);
            if (delegationTable == null) {
                return currentLexer;
            }
            LanguageSupportFactory newLexer = delegationTable.get(tokenType);
            return newLexer == null ? currentLexer : newLexer;
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
