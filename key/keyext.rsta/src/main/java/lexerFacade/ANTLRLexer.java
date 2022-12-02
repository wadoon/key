package lexerFacade;

import lexerFacade.Lexer;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.IntegerStack;
import org.antlr.v4.runtime.misc.Pair;

import java.lang.reflect.Field;
import java.util.HashMap;
import java.util.Map;

public class ANTLRLexer implements Lexer {

    public CharStream _input;
    protected Pair<TokenSource, CharStream> _tokenFactorySourcePair;

    private Token _token;

    private int _tokenStartCharIndex = -1;

    private int _tokenStartLine;

    private int _tokenStartCharPositionInLine;

    private boolean _hitEOF;

    private int _channel;

    private int _type;

    private IntegerStack _modeStack = new IntegerStack();
    private int _mode = org.antlr.v4.runtime.Lexer.DEFAULT_MODE;

    private String _text;


    private final Class<? extends org.antlr.v4.runtime.Lexer> lexerClass;

    private final org.antlr.v4.runtime.Lexer lexer;
    private Token token = CommonTokenFactory.DEFAULT.create(Token.INVALID_TYPE,"");

    public ANTLRLexer(org.antlr.v4.runtime.Lexer lexer) {
        this.lexer = lexer;
        this.lexerClass = lexer.getClass();
    }

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

    /*
    @Override
    public boolean saveStatusBeforeHitEOF() {
        this._text = lexer._text;
        this._input = lexer._input;
        this._hitEOF = lexer._hitEOF;
        this._channel = lexer._channel;
        this._mode = lexer._mode;
        this._token = lexer._token;
        this._modeStack = lexer._modeStack;
        this._tokenStartCharIndex = lexer._tokenStartCharIndex;
        this._tokenStartCharPositionInLine = lexer._tokenStartCharPositionInLine;
        this._tokenStartLine = lexer._tokenStartLine;
        this._type = lexer._type;
        return true;
    }

    @Override
    public boolean resumeOldStatusWithNewInput(String input) {
        lexer._input = new ANTLRInputStream(input);
        lexer._hitEOF = this._hitEOF;
        lexer._mode = this._mode;
        lexer._channel = this._channel;
        lexer._modeStack.clear();
        lexer._modeStack.addAll(this._modeStack);
        lexer._text = this._text;
        lexer._token = this._token;
        lexer._tokenStartCharIndex = this._tokenStartCharIndex;
        lexer._tokenStartCharPositionInLine = this._tokenStartCharPositionInLine;
        lexer._tokenStartLine = this._tokenStartLine;
        lexer._type = this._type;
        return true;
    }


    @Override
    public Map<Integer, String> tokenNames() {
        Map<Integer, String> tokenTypeMap = new HashMap<>();

        try {
            Field f = lexerClass.getDeclaredField("VOCABULARY");
            f.setAccessible(true);

            Vocabulary vocabulary = (Vocabulary) f.get(lexer);

            for (int i = 0; i < vocabulary.getMaxTokenType()+1; i++) {
                tokenTypeMap.put(i, vocabulary.getSymbolicName(i));
            }
            return tokenTypeMap;
        } catch (IllegalAccessException e) {
            e.printStackTrace();
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
        return null;
    }*/

}
