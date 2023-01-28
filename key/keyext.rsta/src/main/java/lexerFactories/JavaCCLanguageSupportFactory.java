package lexerFactories;

import javacc.PositionStream;
import javacc.SimpleCharStream;
import javacc.Token;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import lexerFacade.Lexer;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import javax.json.Json;
import javax.json.JsonObject;
import javax.json.JsonReader;
import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.io.StringReader;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

public class JavaCCLanguageSupportFactory implements LanguageSupportFactory {

    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(JavaCCLanguageSupportFactory.class);

    private Class<? extends Lexer> parserClass;

    private Map<Integer, String> tokenTypeMap;

    public JavaCCLanguageSupportFactory(Class<? extends Lexer> parserClass) {
        this.parserClass = parserClass;
    }

    @Nullable
    @Override
    public Lexer create(String toLex) {
        InputStream targetStream = new ByteArrayInputStream(toLex.getBytes(StandardCharsets.UTF_8));
        try {
            return parserClass.getConstructor(InputStream.class).newInstance(targetStream);
        } catch (InstantiationException | IllegalAccessException | InvocationTargetException e) {
            // TODO
            throw new RuntimeException(e);
        } catch (NoSuchMethodException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public Map<Integer, String> allTokenTypeNames() {
        if (tokenTypeMap != null) {
            return tokenTypeMap;
        }

        tokenTypeMap = new HashMap<>();
        Object tokenManager;
        InputStream targetStream = new ByteArrayInputStream("".getBytes(StandardCharsets.UTF_8));
        try {
            tokenManager = parserClass.getConstructor(InputStream.class).newInstance(targetStream);
        } catch (InstantiationException | IllegalAccessException | InvocationTargetException |
                 NoSuchMethodException e) {
            LOGGER.error(e.getMessage());
            return tokenTypeMap;
        }
        for (Field field: parserClass.getFields()) {
            if (field.getType().equals(int.class)) {
                try {
                    tokenTypeMap.put((Integer) field.get(tokenManager), field.getName());
                } catch (Exception e) {
                    LOGGER.error(e.getMessage());
                }
            }
        }
        return tokenTypeMap;
    }

    @Override
    public SyntaxScheme getSyntaxScheme() {
        String fileName = "defaultScheme.json";

        InputStream jsonFile = JavaCCLanguageSupportFactory.class
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
        return null;
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(parserClass);
    }

    @Override
    public boolean equals(Object other) {
        if (!other.getClass().equals(this.getClass())) {
            return false;
        }
        JavaCCLanguageSupportFactory o = (JavaCCLanguageSupportFactory) other;
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
        return parserClass.equals(o.parserClass);
    }
}
