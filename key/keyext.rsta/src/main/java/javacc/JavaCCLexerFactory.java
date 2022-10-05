package javacc;

import javacc.Token;
import javacc.TokenManager;

public interface JavaCCLexerFactory {

    /**
     * Create a JavaCC TokenManager for the grammar this factory belongs to.
     *
     * @param stream the input for the token manager
     * @return
     */
    TokenManager create(PositionStream stream);

    PositionStream createStream(String input);

    /**
     * By default, the EOF kind is 0.
     *
     * @return an EOF token's integer kind of the corresponding JavaCC grammar
     *          (according to its <Grammar>Constants interface)
     */
    default int eof() {
            return 0;
        }

    /**
     * By default, an EOF token has the image "<EOF>".
     *
     * @return an EOF token for the JavaCC grammar this factory is related to.
     */
    default Token eofToken() {
        Token eof = Token.newToken(eof());
        eof.image = "<EOF>";
        eof.beginLine = 0;
        eof.endLine = 0;
        eof.beginColumn = 0;
        eof.endColumn = 0;
        return eof;
    }

}
