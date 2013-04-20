package se.gu.svanefalk.tackey.editor.syntaxcoloring;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.Token;

import se.gu.svanefalk.tackey.constants.TacletSourceElements;
import se.gu.svanefalk.tackey.editor.rules.RuleUtils;

/**
 * Identifies Taclet keywords, together with their operands (if any).
 * 
 * @author christopher
 * 
 */
public class TacletSourceKeywordRule extends MultiLineRule {

    private static final char BACKSLASH = '\\';

    private static final char CLOSING_PARENTHESIS = ')';
    public static IToken KEYWORD_TOKEN = new Token(
            TacletSourceElements.STATEMENT);
    private static final char OPENING_PARENTHESIS = '(';

    public TacletSourceKeywordRule() {
        super("\\", "", TacletSourceKeywordRule.KEYWORD_TOKEN);
    }



    @Override
    protected boolean endSequenceDetected(final ICharacterScanner scanner) {

        /*
         * Keeps track of the number of braces remaining to close.
         */
        int parenthesesToClose = 0;

        /*
         * Keeps track of the reads done from the first encountered whitespace
         * (in the event that the search fails and we have to unwind).
         */
        int charsRead = 0;

        /*
         * The current character
         */
        char currentChar = 0;

        /*
         * Flags that we have seen at least one opening parentheses.
         */
        boolean sawParenthesis = false;

        /*
         * Flags that we have seen at least one whitespace
         */
        boolean sawWhitespace = false;

        // Do a single unwind, since we will miss the leading backslash
        // otherwise.
        scanner.unread();

        while (true) {

            currentChar = (char) scanner.read();

            if (sawWhitespace || RuleUtils.isWhitespace(currentChar)) {
                if (!sawWhitespace) {
                    sawWhitespace = true;
                }
                charsRead++;
            }

            /*
             * scan until an opening parenthesis is found.
             */
            if (currentChar == TacletSourceKeywordRule.OPENING_PARENTHESIS) {
                if (!sawParenthesis) {
                    sawParenthesis = true;
                }
                parenthesesToClose++;
            }

            if (currentChar == TacletSourceKeywordRule.CLOSING_PARENTHESIS) {
                parenthesesToClose--;
            }

            /*
             * Return true if all parentheses have been closed.
             */
            if (sawParenthesis && (parenthesesToClose == 0)) {
                return true;
            }

            /*
             * The search fails in the event that we encounter a new backslash,
             * indicating the beginning of another keyword.
             */
            if ((currentChar == TacletSourceKeywordRule.BACKSLASH)
                    && (charsRead > 1)) {
                RuleUtils.unwindScanner(scanner, charsRead);
                return false;
            }

            /*
             * Finally, the search fails in the event that we encounter EOF.
             * FIXME: needs to unwind
             */
            if ((currentChar < 0) || (currentChar > 256)) {
                if (!sawParenthesis) {
                    RuleUtils.unwindScanner(scanner, charsRead);
                    return true;
                }
                return super.endSequenceDetected(scanner);
            }
        }
    }
}