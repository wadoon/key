package se.gu.svanefalk.tackey.editors;

import java.util.regex.Pattern;

import org.eclipse.jface.text.rules.IWordDetector;

public class KeywordDetector implements IWordDetector {

    private KeywordDetector() {

    }

    private static KeywordDetector instance = null;

    /**
     * A keyword can consist of any sequence of latin letters.
     */
    private final Pattern keywordPartRegex = Pattern.compile("[a-zA-Z]");

    /**
     * Keywords always start with a backslash...
     */
    @Override
    public boolean isWordStart(char c) {
        boolean returnval = String.valueOf(c).equals("\\");
        return returnval;
    }

    /**
     * ...and may contain any of the latin letters, terminated either by a
     * whitespace or an opening parentheses.
     */
    @Override
    public boolean isWordPart(char c) {
        return keywordPartRegex.matcher(String.valueOf(c)).matches();
    }

    public static KeywordDetector getInstance() {
        if (instance == null) {
            instance = new KeywordDetector();
        }
        return instance;
    }
}
