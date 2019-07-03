package de.uka.ilkd.key.pp;

import org.jetbrains.annotations.NotNull;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Helper class for pretty printing of indices.
 * <p>
 * Indices are replaced by appropriate unicode characters.
 *
 * @author Alexander Weigl
 * @version 1 (03.07.19)
 */
public class PrintingIndicesUtil {
    /**
     * Matches indices at the end of a string, e.g. <code>name_111</code>
     */
    private static Pattern regex = Pattern.compile("_(\\d+)$");

    /**
     * Replaces an index in the given string <code>s</code> with an appropriate sequence
     * of unicode character.
     * <p>
     * If <code>s</code> does not contain an index, <code>s</code> is returned.
     */
    @NotNull
    public static String rewriteIndices(@NotNull String s) {
        Matcher m = regex.matcher(s);
        if (m.find()) {
            String replacement = getUnicodeIndices(m.group(1));
            return s.substring(0, m.start()) + replacement;
        }
        return s;
    }

    public static String getUnicodeIndices(char c) {
        char zeroIndices = '\u2080';
        return "" + (char) (zeroIndices + (c - '0'));
    }

    public static String getUnicodeIndices(String group) {
        switch (group.length()) {
            case 0:
                return "";
            case 1:
                return getUnicodeIndices(group.charAt(0));
            case 2:
                return getUnicodeIndices(group.charAt(0))
                        + "" + getUnicodeIndices(group.charAt(1));
            default:
                StringBuilder sb = new StringBuilder();
                for (int i = 0; i < group.length(); i++) {
                    sb.append(getUnicodeIndices((group.charAt(i))));
                }
                return sb.toString();
        }
    }
}
