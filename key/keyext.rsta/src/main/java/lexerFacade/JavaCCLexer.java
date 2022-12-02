package lexerFacade;

import javacc.PositionStream;
import javacc.Token;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

public class JavaCCLexer implements Lexer {

    private Token token;

    // TODO maybe just the type?
    private final Token eofToken;
    private final Constructor<?> constructor;
    private final Method nextTokenMethod;
    private final PositionStream stream;

    public JavaCCLexer(PositionStream stream, Constructor<?> constructor, Method nextTokenMethod, Token eofToken) {
        this.eofToken = eofToken;
        this.constructor = constructor;
        this.nextTokenMethod = nextTokenMethod;
        this.stream = stream;
    }

    @Override
    public void step() {
        Object tokenManager;

        try {
            tokenManager = constructor.newInstance(stream);
        } catch (InstantiationException | IllegalAccessException | InvocationTargetException e) {
            // TODO
            throw new RuntimeException(e);
        }

        try {
            token = (Token) nextTokenMethod.invoke(tokenManager);
        } catch (IllegalAccessException | InvocationTargetException e) {
            // TODO
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
        return eofToken.kind;
    }

}
