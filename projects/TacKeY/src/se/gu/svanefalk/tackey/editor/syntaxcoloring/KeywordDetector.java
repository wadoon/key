package se.gu.svanefalk.tackey.editor.syntaxcoloring;

import java.util.regex.Pattern;

import org.eclipse.jface.text.rules.IWordDetector;

public class KeywordDetector implements IWordDetector {

    private static KeywordDetector instance = null;

    public static KeywordDetector getInstance() {
        if (KeywordDetector.instance == null) {
            KeywordDetector.instance = new KeywordDetector();
        }
        return KeywordDetector.instance;
    }

    /**
     * A keyword can consist of any sequence of latin letters.
     */
    private final Pattern keywordPartRegex = Pattern.compile("[a-zA-Z]");

    private KeywordDetector() {

    }

    /**
     * ...and may contain any of the latin letters, terminated either by a
     * whitespace or an opening parentheses.
     */
    @Override
    public boolean isWordPart(final char c) {
        return this.keywordPartRegex.matcher(String.valueOf(c)).matches();
    }

    /**
     * Keywords always start with a backslash...
     */
    @Override
    public boolean isWordStart(final char c) {
        final boolean returnval = String.valueOf(c).equals("\\");
        return returnval;
    }
}
