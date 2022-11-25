package lexerFactories;

import javacc.PositionStream;
import javacc.SimpleCharStream;
import javacc.Token;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import rsta.Lexer;
import rsta.LanguageSupportFactory;

import javax.annotation.Nullable;
import java.io.StringReader;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Map;

public class JavaCCLanguageSupportFactory implements LanguageSupportFactory {

    private Class<?> tokenMgrClass;
    private Constructor<?> constructor;
    private Method nextTokenMethod;

    public JavaCCLanguageSupportFactory(Class<?> tokenMgrClass) {
        check(tokenMgrClass);
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
     * TODO make this less scuffed
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
        return new Lexer() {

            Token token;

            @Override
            public void step() {
                Object tokenManager = null;

                try {
                    tokenManager = constructor.newInstance(stream);
                } catch (InstantiationException | IllegalAccessException | InvocationTargetException e) {
                    throw new RuntimeException(e);
                }

                try {
                    token = (Token) nextTokenMethod.invoke(tokenManager);
                } catch (IllegalAccessException | InvocationTargetException e) {
                    throw new RuntimeException(e);
                }
            }

            @Override
            public boolean finished() {
                return token.kind != eofTokenType();
            }

            @Override
            public String lastConsumedTokenText() {
                return token.image;
            }

            @Override
            public Integer lastConsumedTokenStartIndex() {
                return stream.getPos(token.beginLine, token.beginColumn);
            }

            @Override
            public Integer lastConsumedTokenType() {
                return token.kind;
            }

            @Override
            public Integer eofTokenType() {
                return eofToken().kind;
            }

            @Override
            public String eofTokenText() {
                return eofToken().image;
            }
        };
    }

    @Override
    public Map<Integer, String> allTokenTypeNames() {
        // TODO
        return null;
    }

    @Override
    public SyntaxScheme getSyntaxScheme() {
        // TODO get actual grammar file name here, instead of assuming sth. about the class name
        SyntaxScheme scheme = LanguageSupportFactory.createSyntaxScheme(
                tokenMgrClass.getName().substring(0,
                        tokenMgrClass.getName().length() - "TokenManager".length()));
        return scheme;
    }
}
