package se.gu.svanefalk.tackey.editor.rules;

import org.eclipse.jface.text.rules.ICharacterScanner;

public final class RuleUtils {

    public static void unwindScanner(ICharacterScanner scanner, int unwindings) {
        for (int i = 0; i < unwindings; i++) {
            scanner.unread();
        }
    }

    public static boolean isWhitespace(char c) {
        return (c == ' ' || c == '\t' || c == '\n' || c == '\r');
    }
}
