package lexerFacade;

import org.antlr.v4.runtime.misc.IntegerStack;

/**
 * A unified lexer interface used for {@link LexerTokenMaker}.
 */
public interface Lexer {

    /**
     * @return true iff the lexer reached some kind of EOF
     */
    boolean finished();

    int getMode();

    void setMode(int mode);

    void pushMode(int mode);

    int popMode();

    IntegerStack getModeStack();

    /**
     * Consume the next token and hide it behind a TokenFacade object.
     * @return
     */
    TokenFacade nextToken();

}
