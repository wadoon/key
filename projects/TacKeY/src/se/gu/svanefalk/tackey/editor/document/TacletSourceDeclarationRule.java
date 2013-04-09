package se.gu.svanefalk.tackey.editor.document;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.Token;

import se.gu.svanefalk.tackey.editor.TacletSourceElements;


public class TacletSourceDeclarationRule extends MultiLineRule {

    public static IToken DECLARATION_TOKEN = new Token(
            TacletSourceElements.DECLARATION);

    /**
     * As this rule is only applicable once per taclet, we flag it as used as
     * soon as it has returned a positive result.
     */
    private boolean hasSucceeded = false;

    private static final char OPENING_CURLYBRACE = '{';

    public TacletSourceDeclarationRule() {
        super(" ", " ", DECLARATION_TOKEN);
    }

    @Override
    protected boolean sequenceDetected(ICharacterScanner scanner,
            char[] sequence, boolean eofAllowed) {
        return !hasSucceeded;
    }

    @Override
    protected boolean endSequenceDetected(ICharacterScanner scanner) {
        if (hasSucceeded) {
            return false;
        }

        /*
         * Number of characters processed, in case we have to unwind.
         */
        int readCharacters = 0;

        /*
         * The current character being processed
         */
        char currentChar = 0;

        while (true) {

            currentChar = (char) scanner.read();
            
            /*
             * Finish iff. we encounter an opening curly brace.
             */
            if (currentChar == OPENING_CURLYBRACE) {
                scanner.unread();
                hasSucceeded = true;
                return true;
            }

            if ((int) currentChar < 0 || (int) currentChar > 256) {
                return super.endSequenceDetected(scanner);
            }
        }
    }
}