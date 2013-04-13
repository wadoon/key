package se.gu.svanefalk.tackey.editor.document;

import java.util.regex.Pattern;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.Token;

import se.gu.svanefalk.tackey.constants.TacletSourceElements;
import se.gu.svanefalk.tackey.editor.rules.RuleUtils;

public class TacletSourceDeclarationRule extends MultiLineRule {
    private TacletSourceDeclarationRule(String startSequence,
            String endSequence, IToken token) {
        super(startSequence, endSequence, token);
    }

    private final Pattern latinLetterRegex = Pattern.compile("[a-zA-Z]");

    private static final char OPENING_CURLYBRACE = '{';
    private static final char CLOSING_CURLYBRACE = '}';
    private static final char SEMICOLON = ';';

    /**
     * As this rule is only applicable once per taclet, we flag it as used as
     * soon as it has returned a positive result.
     */
    // private boolean hasSucceeded = false;

    /**
     * Customize the evaluation function to handle cases where there is no
     * definitive starting sequence
     */
    @Override
    protected IToken doEvaluate(ICharacterScanner scanner, boolean resume) {

        if (resume) {

            if (endSequenceDetected(scanner))
                return fToken;

        } else {

            int c = scanner.read();
            if (sequenceDetected(scanner, fStartSequence, fBreaksOnEOF)) {
                if (endSequenceDetected(scanner))
                    return fToken;
            }
        }
        scanner.unread();
        return Token.UNDEFINED;
    }

    /**
     * This rule can start at any character in the latin alphabet
     */
    @Override
    protected boolean sequenceDetected(ICharacterScanner scanner,
            char[] sequence, boolean eofAllowed) {

        char character = (char) scanner.read();
        boolean match = latinLetterRegex.matcher(String.valueOf(character)).matches();
        scanner.unread();
        return match;
    }

    @Override
    protected boolean endSequenceDetected(final ICharacterScanner scanner) {

        /*
         * The current character being processed
         */
        char currentChar = 0;

        /*
         * Chars read
         */
        int charsRead = 0;

        /*
         * Flags if we have seen an opening curly brace yet.
         */
        boolean sawOpeningBrace = false;

        /*
         * Counts the number of braces to close.
         */
        int bracesToClose = 0;

        String debug = "";

        while (true) {

            currentChar = (char) scanner.read();

            charsRead++;
            debug += currentChar;

            /*
             * scan until an opening parenthesis is found.
             */
            if (currentChar == OPENING_CURLYBRACE) {
                if (!sawOpeningBrace) {
                    sawOpeningBrace = true;
                }
                bracesToClose++;
            }

            if (currentChar == CLOSING_CURLYBRACE) {
                bracesToClose--;
            }

            /*
             * Return true if all parentheses have been closed.
             */
            if (currentChar == CLOSING_CURLYBRACE && sawOpeningBrace
                    && (bracesToClose == 0)) {
                return true;
            }

            if ((currentChar < 0) || (currentChar > 256)) {
                RuleUtils.unwindScanner(scanner, charsRead);
                return super.endSequenceDetected(scanner);
            }
        }
    }

    public static TacletSourceDeclarationRule createDefaultInstance() {

        IToken declarationToken = new Token(TacletSourceElements.DECLARATION);

        return createCustomInstance(declarationToken);
    }

    public static TacletSourceDeclarationRule createCustomInstance(IToken token) {

        return new TacletSourceDeclarationRule(" ", " ", token);
    }
}