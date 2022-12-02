package lexerFactories;

import javacc.PositionStream;
import javacc.SimpleCharStream;
import javacc.Token;
import lexerFacade.JavaCCLexer;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import lexerFacade.Lexer;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import javax.json.Json;
import javax.json.JsonObject;
import javax.json.JsonReader;
import java.io.InputStream;
import java.io.StringReader;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

public class JavaCCLanguageSupportFactory implements LanguageSupportFactory {

    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(JavaCCLanguageSupportFactory.class);

    private Class<?> tokenMgrClass;
    private Constructor<?> constructor;
    private Method nextTokenMethod;

    public JavaCCLanguageSupportFactory(Class<?> tokenMgrClass) {
        if (!check(tokenMgrClass)) {
            String msg = tokenMgrClass.getName() + " is not a JavaCC token maker.";
            LOGGER.error(msg);
            throw new IllegalArgumentException(msg);
        }
        this.tokenMgrClass = tokenMgrClass;
    }

    protected PositionStream makeStream(String input) {
        return new SimpleCharStream(new StringReader(input), 0, 0);
    }

    /**
     * By default, an EOF token has the image "<EOF>".
     *
     * @return an EOF token for the JavaCC grammar this factory is related to.
     */
    protected Token eofToken() {
        int eofKind = 0;
        Token eof = Token.newToken(eofKind);
        eof.image = "<EOF>";
        eof.beginLine = 0;
        eof.endLine = 0;
        eof.beginColumn = 0;
        eof.endColumn = 0;
        return eof;
    }

    /**
     * TODO make this less scuffed?
     */
    private boolean check(Class<?> tokenMgrClass) {
        try {
            this.constructor = tokenMgrClass.getDeclaredConstructor(SimpleCharStream.class);
        } catch (NoSuchMethodException | SecurityException e) {
            return false;
        }
        try {
            this.nextTokenMethod = tokenMgrClass.getDeclaredMethod("getNextToken");
        } catch (NoSuchMethodException | SecurityException e) {
            return false;
        }
        return true;
    }

    @Nullable
    @Override
    public Lexer create(String toLex) {
        PositionStream stream = makeStream(toLex);
        return new JavaCCLexer(stream, constructor, nextTokenMethod, eofToken());
    }

    @Override
    public Map<Integer, String> allTokenTypeNames() {
        Map<Integer, String> tokenTypeNames = new HashMap<>();
        Object tokenManager;
        try {
            tokenManager = constructor.newInstance(makeStream(""));
        } catch (InstantiationException | IllegalAccessException | InvocationTargetException e) {
            LOGGER.error(e.getMessage());
            return tokenTypeNames;
        }
        for (Field field: tokenMgrClass.getDeclaredFields()) {
            if (field.getType().equals(Integer.class)) {
                try {
                    tokenTypeNames.put((Integer) field.get(tokenManager), field.getName());
                } catch (Exception e) {
                    LOGGER.error(e.getMessage());
                }
            }
        }
        return tokenTypeNames;
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
}
