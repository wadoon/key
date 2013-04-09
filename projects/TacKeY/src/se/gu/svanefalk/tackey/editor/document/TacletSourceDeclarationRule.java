package se.gu.svanefalk.tackey.editor.document;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.Token;

import se.gu.svanefalk.tackey.constants.TacletSourceElements;

public class TacletSourceDeclarationRule extends MultiLineRule {

    public static IToken DECLARATION_TOKEN = new Token(
            TacletSourceElements.DECLARATION);

    private static final char OPENING_CURLYBRACE = '{';

    /**
     * As this rule is only applicable once per taclet, we flag it as used as
     * soon as it has returned a positive result.
     */
    private boolean hasSucceeded = false;

    public TacletSourceDeclarationRule() {
        super(" ", " ", TacletSourceDeclarationRule.DECLARATION_TOKEN);
    }

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

            if (sequenceDetected(scanner, fStartSequence, fBreaksOnEOF)) {
                if (endSequenceDetected(scanner))
                    return fToken;
            }
        }

        return Token.UNDEFINED;
    }

    @Override
    protected boolean endSequenceDetected(final ICharacterScanner scanner) {
        if (this.hasSucceeded) {
            return false;
        }

        /*
         * The current character being processed
         */
        char currentChar = 0;

        while (true) {

            currentChar = (char) scanner.read();

            /*
             * Finish iff. we encounter an opening curly brace.
             */
            if (currentChar == TacletSourceDeclarationRule.OPENING_CURLYBRACE) {
                scanner.unread();
                this.hasSucceeded = true;
                return true;
            }

            if ((currentChar < 0) || (currentChar > 256)) {
                return super.endSequenceDetected(scanner);
            }
        }
    }

    @Override
    protected boolean sequenceDetected(final ICharacterScanner scanner,
            final char[] sequence, final boolean eofAllowed) {
        return !this.hasSucceeded;
    }
}