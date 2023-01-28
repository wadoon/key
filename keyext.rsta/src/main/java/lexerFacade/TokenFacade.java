package lexerFacade;

import java.util.Arrays;

public class TokenFacade {

    public final int tokenType, startIndex, stopIndex;
    public final String text;
    private final TokenFacade[] alternatives;

    public TokenFacade(int tokenType, int startIndex, String text, TokenFacade... alternatives) {
        this.tokenType = tokenType;
        this.startIndex = startIndex;
        this.stopIndex = startIndex + text.length() - 1;
        this.text = text;
        this.alternatives = alternatives;
    }

    /**
     * Sometimes multiple tokens can be matched with a String or a prefix of the String.
     * A lexer chooses one of those tokens according to some rules, e.g. by first creating the longest
     * possible match and then choosing the token that was defined first in the grammar file (ANTLR).
     * The other tokens that might occur at this token's position, had the lexer followed a different
     * choice policy, are those whose rules match {@link #text} or a prefix of that.
     *
     * @return all tokens that might have occurred at this token's position, had the lexer chosen differently
     */
    public TokenFacade[] getAlternatives() {
        return Arrays.copyOf(alternatives, alternatives.length);
    }
}
