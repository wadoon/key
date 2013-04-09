package se.gu.svanefalk.tackey.editor;

import org.eclipse.jface.text.rules.IWhitespaceDetector;

public class WhitespaceDetector implements IWhitespaceDetector {

    private static WhitespaceDetector instance = null;

    public static WhitespaceDetector getInstance() {
        if (WhitespaceDetector.instance == null) {
            WhitespaceDetector.instance = new WhitespaceDetector();
        }
        return WhitespaceDetector.instance;
    }

    private WhitespaceDetector() {
    }

    @Override
    public boolean isWhitespace(final char c) {
        return ((c == ' ') || (c == '\t') || (c == '\n') || (c == '\r'));
    }
}
