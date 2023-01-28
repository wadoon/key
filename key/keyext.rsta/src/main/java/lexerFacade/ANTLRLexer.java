package lexerFacade;

import lexerFacade.Lexer;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.IntegerStack;
import org.antlr.v4.runtime.misc.Pair;

import java.lang.reflect.Field;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

public class ANTLRLexer implements Lexer {

    private IntegerStack _modeStack = new IntegerStack();
    private int _mode = org.antlr.v4.runtime.Lexer.DEFAULT_MODE;
    private final Class<? extends org.antlr.v4.runtime.Lexer> lexerClass;

    private final org.antlr.v4.runtime.Lexer lexer;
    private Token token = CommonTokenFactory.DEFAULT.create(Token.INVALID_TYPE,"<INVALID>");

    public ANTLRLexer(org.antlr.v4.runtime.Lexer lexer) {
        this.lexer = lexer;
        this.lexerClass = lexer.getClass();
    }

    @Override
    public boolean finished() {
        return lexer._hitEOF;
    }

    @Override
    public int getMode() {
        return lexer._mode;
    }

    @Override
    public void setMode(int mode) {
        lexer._mode = mode;
    }

    @Override
    public void pushMode(int mode) {
        lexer.pushMode(mode);
    }

    @Override
    public int popMode() {
        return lexer.popMode();
    }

    @Override
    public IntegerStack getModeStack() {
        return new IntegerStack(lexer._modeStack);
    }

    @Override
    public TokenFacade nextToken() {
        token = lexer.nextToken();
        // TODO alternatives (for really valid multiline line-by-line lexing)
        return new TokenFacade(token.getType(), token.getStartIndex(), token.getText());
    }

    @Override
    public String toString() {
        return "ANTLRLexer for " + lexerClass.getName() + " on " + lexer._input;
    }

}
