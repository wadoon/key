package se.gu.svanefalk.tackey.editor.rules;

import org.eclipse.jface.text.rules.ICharacterScanner;

public final class RuleUtils {

    public static boolean isWhitespace(final char c) {
        return ((c == ' ') || (c == '\t') || (c == '\n') || (c == '\r'));
    }

    public static void unwindScanner(final ICharacterScanner scanner,
            final int unwindings) {
        for (int i = 0; i < unwindings; i++) {
            scanner.unread();
        }
    }
}
