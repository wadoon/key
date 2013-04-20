package se.gu.svanefalk.tackey.editor.syntaxcoloring;

import java.util.regex.Pattern;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * Instances of this detector will pass all words containing the standard latin
 * letters.
 * 
 * @author christopher
 * 
 */
public class NonNumericDetector implements IWordDetector {

    private static NonNumericDetector instance = null;

    public static NonNumericDetector getInstance() {
        if (NonNumericDetector.instance == null) {
            NonNumericDetector.instance = new NonNumericDetector();
        }
        return NonNumericDetector.instance;
    }

    private final Pattern latinLetterRegex = Pattern.compile("[a-zA-Z]");

    private NonNumericDetector() {

    }

    @Override
    public boolean isWordPart(final char c) {
        return this.latinLetterRegex.matcher(String.valueOf(c)).matches();
    }

    @Override
    public boolean isWordStart(final char c) {
        return this.latinLetterRegex.matcher(String.valueOf(c)).matches();
    }

}
