package lexerFactories;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.Vocabulary;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import rsta.AutomaticSyntaxScheme;
import rsta.Lexer;
import rsta.LanguageSupportFactory;

import javax.annotation.Nullable;
import javax.json.Json;
import javax.json.JsonObject;
import javax.json.JsonReader;
import java.io.InputStream;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Map;

public class ANTLRLanguageSupportFactory implements LanguageSupportFactory {

    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(ANTLRLanguageSupportFactory.class);

    private Class<org.antlr.v4.runtime.Lexer> lexerClass;

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

        return new Lexer() {

            Token token;

            @Override
            public void step() {
                token = lexer.nextToken();
            }

            @Override
            public boolean finished() {
                return lexer._hitEOF;
            }

            @Override
            public String lastConsumedTokenText() {
                return token.getText();
            }

            @Override
            public Integer lastConsumedTokenStartIndex() {
                return token.getStartIndex();
            }

            @Override
            public Integer lastConsumedTokenType() {
                return token.getType();
            }

            @Override
            public Integer eofTokenType() {
                return Token.EOF;
            }

            @Override
            public String eofTokenText() {
                return "<EOF>";
            }

        };
    }

    @Nullable
    @Override
    public Map<Integer, String> allTokenTypeNames() {
        Map<Integer, String> tokenTypeMap = new HashMap<>();

        try {
            Field f = lexerClass.getDeclaredField("VOCABULARY");
            f.setAccessible(true);

            Vocabulary vocabulary = (Vocabulary) f.get(makeLexer(lexerClass, ""));

            for (int i = 0; i < vocabulary.getMaxTokenType()+1; i++) {
                tokenTypeMap.put(i, vocabulary.getSymbolicName(i));
            }
        } catch (NoSuchMethodException | InvocationTargetException
                 | InstantiationException | IllegalAccessException e) {
            e.printStackTrace();
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
        return null;
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

    private static org.antlr.v4.runtime.Lexer makeLexer(
            Class<org.antlr.v4.runtime.Lexer> lexerClass, String input)
            throws NoSuchMethodException, InvocationTargetException,
            InstantiationException, IllegalAccessException {
        return lexerClass
                .getConstructor(CharStream.class)
                // TODO use sth that is not deprecated
                .newInstance(new ANTLRInputStream(input));
    }
}
