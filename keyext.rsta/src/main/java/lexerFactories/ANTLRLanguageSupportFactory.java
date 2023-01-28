package lexerFactories;

import lexerFacade.ANTLRLexer;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Vocabulary;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import lexerFacade.Lexer;

import javax.annotation.Nullable;
import javax.json.Json;
import javax.json.JsonObject;
import javax.json.JsonReader;
import java.io.InputStream;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

public class ANTLRLanguageSupportFactory implements LanguageSupportFactory {

    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(ANTLRLanguageSupportFactory.class);

    private Class<org.antlr.v4.runtime.Lexer> lexerClass;

    private Map<Integer, String> tokenTypeMap;

    private Map<Integer, String> modeMap;

    public ANTLRLanguageSupportFactory(Class<org.antlr.v4.runtime.Lexer> lexerClass) {
        this.lexerClass = lexerClass;
    }

    @Override
    public Lexer create(String toLex) {

        org.antlr.v4.runtime.Lexer lexer;

        try {
            lexer = makeLexer(lexerClass, toLex);
        } catch (NoSuchMethodException | InvocationTargetException
                 | InstantiationException | IllegalAccessException e) {
            return null;
        }

        return new ANTLRLexer(lexer);
    }

    @Nullable
    @Override
    public Map<Integer, String> allTokenTypeNames() {
        if (tokenTypeMap != null) {
            return tokenTypeMap;
        }

        tokenTypeMap = new HashMap<>();

        try {
            Vocabulary vocabulary = makeLexer(lexerClass, "").getVocabulary();

            for (int i = 0; i < vocabulary.getMaxTokenType()+1; i++) {
                tokenTypeMap.put(i, vocabulary.getSymbolicName(i));
            }
        } catch (NoSuchMethodException | InvocationTargetException
                 | InstantiationException | IllegalAccessException e) {
            LOGGER.warn(e.getMessage());
        }
        return tokenTypeMap;
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
        if (modeMap != null) {
            return modeMap;
        }

        modeMap = new HashMap<>();

        try {
            String[] modes = makeLexer(lexerClass, "").getModeNames();

            for (int i = 0; i < modes.length; i++) {
                modeMap.put(i, modes[i]);
            }
        } catch (NoSuchMethodException | InvocationTargetException
                 | InstantiationException | IllegalAccessException e) {
            LOGGER.warn(e.getMessage());
        }
        return modeMap;
    }

    private static org.antlr.v4.runtime.Lexer makeLexer(
            Class<org.antlr.v4.runtime.Lexer> lexerClass, String input)
            throws NoSuchMethodException, InvocationTargetException,
            InstantiationException, IllegalAccessException {
        return lexerClass
                .getConstructor(CharStream.class)
                // TODO use sth that is not deprecated
                .newInstance(new ANTLRInputStream(input));
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(lexerClass);
    }

    @Override
    public boolean equals(Object other) {
        if (!other.getClass().equals(this.getClass())) {
            return false;
        }
        ANTLRLanguageSupportFactory o = (ANTLRLanguageSupportFactory) other;
        if (o.allTokenTypeNames().size() != allTokenTypeNames().size()) {
            return false;
        }
        for (Map.Entry<Integer, String> entry: allTokenTypeNames().entrySet()) {
            if (!o.allTokenTypeNames().entrySet().contains(entry)) {
                return false;
            }
        }
        for (Map.Entry<Integer, String> entry: o.allTokenTypeNames().entrySet()) {
            if (!allTokenTypeNames().entrySet().contains(entry)) {
                return false;
            }
        }
        return lexerClass.equals(o.lexerClass);
    }
}
