package se.gu.svanefalk.tackey.editor.syntaxcoloring;

import java.util.regex.Pattern;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.WordPatternRule;

public class OpenWordPatternRule extends WordPatternRule {

    private final Pattern latinLetterRegex = Pattern.compile("[a-zA-Z]");

    private OpenWordPatternRule(IWordDetector detector, String startSequence,
            String endSequence, IToken token) {
        super(detector, startSequence, endSequence, token);
    }

    public static OpenWordPatternRule createInstance(IWordDetector detector,
            String endSequence, IToken token) {
        return new OpenWordPatternRule(detector, " ", endSequence, token);
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
}