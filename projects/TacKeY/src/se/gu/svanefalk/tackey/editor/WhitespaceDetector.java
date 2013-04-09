package se.gu.svanefalk.tackey.editor;

import org.eclipse.jface.text.rules.IWhitespaceDetector;

public class WhitespaceDetector implements IWhitespaceDetector {

    private static WhitespaceDetector instance = null;

    private WhitespaceDetector() {
    }

    public boolean isWhitespace(char c) {
        return (c == ' ' || c == '\t' || c == '\n' || c == '\r');
    }

    public static WhitespaceDetector getInstance() {
        if (instance == null) {
            instance = new WhitespaceDetector();
        }
        return instance;
    }
}
