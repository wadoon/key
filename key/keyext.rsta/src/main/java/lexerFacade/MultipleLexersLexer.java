package lexerFacade;

import lexerFactories.LanguageSupportFactory;
import org.antlr.v4.runtime.misc.IntegerStack;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import java.util.*;

public class MultipleLexersLexer implements Lexer {

    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(MultipleLexersLexer.class);

    /**
     * The complete String to be lexed.
     */
    private final String toLex;

    /**
     * Stores information for each lexer/lexer factory about where to delegate which token.
     */
    private final LexerDelegationMap lexerDelegationMap;

    /**
     * The first/outermost lexer that starts the lexing process on {@link #toLex}.
     */
    private final Lexer outerLexer;

    /**
     * A list of all lexer factories that might be used by this MultipleLexersLexer.
     * The first element of that list is used as the "outer" factory, i.e. the factory
     * that first creates the {@link #outerLexer} for {@link #toLex}.
     * The created lexer will then delegate its created tokens to other lexers using
     * {@link #lexerDelegationMap}.
     * The list also has to be ordered in order for
     * {@link #evaluateUniqueValue(LanguageSupportFactory, int, Map, int, int)} to be deterministic.
     */
    private final List<LanguageSupportFactory> lexerFactoryOrder;

    /**
     * The maximum amount of different token kinds among all possible lexers/lexer factories
     * from {@link #lexerFactoryOrder}.
     */
    private final int maxTokens;

    /**
     * The maximum amount of different modes among all possible lexers/lexer factories
     * from {@link #lexerFactoryOrder}.
     */
    private final int maxModes;

    /**
     * Temp variables for recursive descent into the responsible lexer.
     */

    /**
     * The currently used lexer factory.
     */
    private LanguageSupportFactory currentFactory;
    /**
     * The currently active lexer.
     */
    private Lexer currentLexer;

    /**
     * Maps the token types per factory to new, global token types that are unique among all
     * token types used by this MultipleLexersLexer.
     */
    private final Map<LanguageSupportFactory, Map<Integer, Integer>> uniqueTokenTypes = new HashMap<>();

    /**
     * Maps the modes per lexer/lexer factory to new, global modes that are unique among all modes
     * used by this MultipleLexersLexer.
     */
    private final Map<LanguageSupportFactory, Map<Integer, Integer>> uniqueModes = new HashMap<>();


    private final Stack<Lexer> lexerStack = new Stack<>();
    private final Stack<LanguageSupportFactory> factoryStack = new Stack<>();


    /**
     * TODO don't use the antlr stack
     */
    private  final IntegerStack modeStack = new IntegerStack();

    /**
     * The currently last consumed token.
     */
    private TokenFacade token;

    /**
     * The current global mode.
     */
    private int mode;

    private boolean finished = false;

    private int curStartIndexGlobal = 0;

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
        OptionalInt maxModes = lexerFactoryOrder.stream()
                .mapToInt(l -> l.allModes() == null ? 0 : l.allModes().entrySet().size())
                .max();
        this.maxTokens = maxTokenAmount.isEmpty() ? 0 : maxTokenAmount.getAsInt();
        this.maxModes = maxModes.isEmpty() ? 0 : maxModes.getAsInt();
    }

    /**
     * Map the given integer value to
     * factor * i + value
     * where i is the index of the given factory in {@link #lexerFactoryOrder}.
     * Note that value < factor must hold for this to return unique mappings among all
     * (factory, value) pairs.
     * If cache already contains a mapping for value, just use that.
     * Otherwise, the evaluated mapping will be added to cache.
     * @param factory
     * @param value
     * @param cache
     * @param factor
     * @return
     */
    private int evaluateUniqueValue(LanguageSupportFactory factory, int value,
                                    Map<LanguageSupportFactory, Map<Integer, Integer>> cache,
                                    int factor) {
        if (value > factor) {
            throw new IllegalArgumentException(value + ">=" + factor + " must not hold!");
        }
        /*
        If a unique value for the given factory and value has already been cached, just return that.
         */
        Map<Integer, Integer> cachedEvaluatedValuesForFactory = cache.get(factory);
        if (cachedEvaluatedValuesForFactory != null) {
            Integer evaluatedType = cachedEvaluatedValuesForFactory.get(value);
            if (evaluatedType != null) {
                return evaluatedType;
            }
        }
        /*
        Otherwise, evaluate the unique value.
         */
        for (int index = 0; index < lexerFactoryOrder.size(); index++) {
            // Make sure the first lexer gets its tokens mapped to their original value to have the EOF tokens match.
            if (lexerFactoryOrder.get(index).equals(factory)) {
                return index*factor+value;
            }
        }
        throw new IllegalArgumentException(factory + " is not contained in the factory list!");
    }

    /**
     * Let the current lexer consume its next token. If the resulting token is to be delegated
     * to another lexer,
     * @return
     */
    @Override
    public TokenFacade nextToken() {
        // If lexing is finished, return null ?
        // TODO ?
        if (finished()) {
            return null;
        }

        // Let the current lexer consume its next token.
        TokenFacade cur = currentLexer.nextToken();
        // The current last consumed token's global type and global start index wrt toLex.
        int curType = evaluateUniqueValue(
            currentFactory, cur.tokenType, uniqueTokenTypes, maxTokens);
        // The lexer (factory) that the current lexer should delegate the last consumed token to.
        LanguageSupportFactory newFactory = lexerDelegationMap.getNextLexer(
            currentFactory, curType);

        /*
        Case 1: The current lexer does not have to delegate its last consumed token.
         */
        // TODO current lexer in some mode -> go back to that mode when returning from child lexer
        if (currentFactory.equals(newFactory)) {
            // TODO the alternative tokens
            // Set the global last consumed token to be the currently last consumed token.
            token = new TokenFacade(curType,
                                    curStartIndexGlobal, cur.text);
            curStartIndexGlobal += token.text.length();
        } else {
        /*
        Case 2: The current lexer consumes the token and has to delegate it further.
         */
            // Remember the current lexer and factory.
            lexerStack.push(currentLexer);
            factoryStack.push(currentFactory);
            // Update the current factory and lexer.
            // The new lexer works only on the current token's text.
            currentFactory = newFactory;
            currentLexer = newFactory.create(cur.text);
            // Recursive lexing delegation to the new current lexer
            // until the responsible lexer is found and steps into Case 1 (see above).
            nextToken();
        }
        // The current lexer should keep doing the next step until it is finished with
        // its given text.
        assert(lexerStack.size() == factoryStack.size());
        // Step back up until a lexer us reached that is not finished yet.
        while (currentLexer.finished() && !lexerStack.isEmpty()) {
            // Once the lexer we delegated to is finished, reset to the previous lexer (factory).
            currentLexer = lexerStack.pop();
            currentFactory = factoryStack.pop();
        }
        // finished if the first lexer reached EOF
        finished = finished || (currentLexer.finished() && lexerStack.size() <= 1);
        // Set the global mode to be the current lexer's global mode.
        mode = evaluateUniqueValue(currentFactory, currentLexer.getMode(), uniqueModes, maxModes);
        return token;
    }

    @Override
    public boolean finished() {
        return finished;
    }

    @Override
    public int getMode() {
        return mode;
    }

    @Override
    public void setMode(int mode) {
        int index = getFactoryIndex(mode);
        LanguageSupportFactory factory = lexerFactoryOrder.get(index);
        // TODO
        if (factory == null) {
            throw new IllegalArgumentException();
        }
        currentFactory = factory;
        currentLexer = currentFactory.create(toLex.substring(curStartIndexGlobal));
        // mode = true_mode + index * maxModes
        // TODO push in pushmode but also call setMode on the corresponding lexer
        currentLexer.pushMode(mode%maxModes);
        this.mode = mode;
    }

    private int getFactoryIndex(int mode) {
        for (int index = 0; index < lexerFactoryOrder.size(); index++) {
            LanguageSupportFactory factory = lexerFactoryOrder.get(index);
            for (int m = 0; m < factory.allModes().size(); m++) {
                if (evaluateUniqueValue(factory, m, uniqueModes, maxModes) == mode) {
                    return index;
                }
            }
        }
        return 0;
    }

    @Override
    public void pushMode(int mode) {
        setMode(mode);
        modeStack.push(mode);
        int index = getFactoryIndex(mode);
        LanguageSupportFactory factory = lexerFactoryOrder.get(index);
        currentFactory = factory;
        currentLexer = currentFactory.create(token == null ? toLex : toLex.substring(curStartIndexGlobal));
        // mode = true_mode + index * maxModes
        currentLexer.pushMode(mode%maxModes);
    }

    @Override
    public int popMode() {
        currentLexer.popMode();
        int poppedMode = modeStack.pop();
        setMode(poppedMode);
        return poppedMode;
    }

    @Override
    public IntegerStack getModeStack() {
        return new IntegerStack(modeStack);
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
