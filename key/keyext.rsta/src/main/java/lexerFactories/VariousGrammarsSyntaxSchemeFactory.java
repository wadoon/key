package lexerFactories;

import lexerFacade.MultipleLexersLexer;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import lexerFacade.Lexer;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import javax.json.Json;
import javax.json.JsonObject;
import javax.json.JsonReader;
import javax.security.auth.callback.LanguageCallback;
import java.io.InputStream;
import java.util.*;

public class VariousGrammarsSyntaxSchemeFactory implements LanguageSupportFactory {

    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(VariousGrammarsSyntaxSchemeFactory.class);
    private final List<LanguageSupportFactory> lexerFactoryOrder;
    private final MultipleLexersLexer.LexerDelegationMap lexerDelegationMap;
    private Map<Integer, String> allTokenTypeNames = new HashMap<>();
    private Map<Integer, String> modes = new HashMap<>();

    public VariousGrammarsSyntaxSchemeFactory(
            List<LanguageSupportFactory> lexerFactoryOrder,
            MultipleLexersLexer.LexerDelegationMap lexerDelegationMap) {
        // TODO create this map via json?
        this.lexerFactoryOrder = new ArrayList<>(lexerFactoryOrder);
        this.lexerDelegationMap = lexerDelegationMap;
        for (LanguageSupportFactory factory: lexerFactoryOrder) {
            Map<Integer, String> map = factory.allTokenTypeNames();
            Map<Integer, String> modeMap = factory.allModes();
            if (map == null) {
                continue;
            }
            for (Map.Entry<Integer, String> mapping : map.entrySet()) {
                //TODO AutomaticSyntaxScheme definition has problems if different tokens have the same name here (they will all be treated the same)
                allTokenTypeNames.put(evaluateTokenType(factory, mapping.getKey()), mapping.getValue());
            }
            if (modeMap == null) {
                continue;
            }
            for (Map.Entry<Integer, String> mapping : modeMap.entrySet()) {
                modes.put(mapping.getKey(), mapping.getValue());
            }
        }
    }

    private int evaluateTokenType(LanguageSupportFactory factory, int tokenType) {
        OptionalInt maxTokenAmount = lexerFactoryOrder.stream()
                .mapToInt(l -> l.allTokenTypeNames() == null ? 0 : l.allTokenTypeNames().entrySet().size())
                .max();
        int maxTokens = maxTokenAmount.isEmpty() ? 0 : maxTokenAmount.getAsInt();
        if (tokenType > maxTokens) {
            return -1;
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
        // TODO does this break stuff?
        /*
        If the given factory does not exist, just return -1;
         */
        return -1;
    }

    @Nullable
    @Override
    public Lexer create(String toLex) {
        return new MultipleLexersLexer(lexerFactoryOrder, lexerDelegationMap, toLex);
    }

    @Override
    public Map<Integer, String> allTokenTypeNames() {
        return allTokenTypeNames;
    }

    @Override
    public SyntaxScheme getSyntaxScheme() {
        String fileName = "defaultScheme.json";

        InputStream jsonFile = ANTLRLanguageSupportFactory.class
                .getResourceAsStream(fileName);
        JsonObject jsonObject = null;
        try {
            JsonReader jsonReader = Json.createReader(jsonFile);
            jsonObject = jsonReader.readObject();
            jsonReader.close();
        } catch (Exception e) {
            // every possible exception should be caught as loading the files
            // should not break key
            // if loading the props file does not work for any reason,
            // create a warning and continue
            LOGGER.warn(String.format("File %s could not be loaded. Reason: %s",
                    fileName, e.getMessage()));
        }

        SyntaxScheme scheme = new AutomaticSyntaxScheme(jsonObject, allTokenTypeNames());

        return scheme;
    }

    @Override
    public Map<Integer, String> allModes() {
        return modes;
    }

    @Override
    public boolean equals(Object other) {
        if (!other.getClass().equals(this.getClass())) {
            return false;
        }
        VariousGrammarsSyntaxSchemeFactory o = (VariousGrammarsSyntaxSchemeFactory) other;
        if (o.lexerFactoryOrder.size() != lexerFactoryOrder.size() || o.allTokenTypeNames.size() != allTokenTypeNames.size()) {
            return false;
        }
        for (Map.Entry<Integer, String> entry: allTokenTypeNames.entrySet()) {
            if (!o.allTokenTypeNames.entrySet().contains(entry)) {
                return false;
            }
        }
        for (Map.Entry<Integer, String> entry: o.allTokenTypeNames.entrySet()) {
            if (!allTokenTypeNames.entrySet().contains(entry)) {
                return false;
            }
        }
        for (LanguageSupportFactory factory: lexerFactoryOrder) {
            if (!o.lexerFactoryOrder.contains(factory)) {
                return false;
            }
        }
        for (LanguageSupportFactory factory: o.lexerFactoryOrder) {
            if (!lexerFactoryOrder.contains(factory)) {
                return false;
            }
        }
        return true;
    }

}
