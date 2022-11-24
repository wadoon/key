package rsta;

/**
 * A unified lexer interface used for {@link LexerTokenMaker}.
 */
public interface Lexer {

    /**
     * Consume the next token.
     * Should impact nextTokenText, nextStartIndex and nextTokenType accordingly.
     */
    void step();

    /**
     * @return true iff the lexer reached some kind of EOF
     */
    boolean finished();

    String nextTokenText();

    Integer nextStartIndex();

    Integer nextTokenType();

    Integer eofTokenType();

    String eofTokenText();
}
