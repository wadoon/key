package de.uka.ilkd.key.nui.filter;

public class LineToPrintedProofPosition {
    /**
     * Resolves the index of a char in the document to a line number.
     * 
     * @param currentChar
     * @param originalLines
     * @return
     */
    public static int getLineIndex(int currentChar, String[] originalLines) {
        if (currentChar < 0)
            throw new IndexOutOfBoundsException();
        int idx = 0;
        for (int line = 0; line < originalLines.length; line++) {
            // add + 1 to count for the line-break at the end of each line that
            // doesn't appear in the split document (thanks to max)
            idx += originalLines[line].length() + 1;
            if (idx > currentChar)
                return line;
        }
        throw new IndexOutOfBoundsException();
    }

    /**
     * Get the position of the first not whitespace char in the string
     * 
     * @param line
     * @return
     */
    public static int getFirstNonWhitespace(String line) {
        for (int notwhite = 0; notwhite < line.length(); notwhite++) {
            if (!Character.isSpaceChar(line.charAt(notwhite))) {
                // return the first non-whitespace char of this line
                return notwhite;
            }
        }
        return 0;
    }

    /**
     * Resolves a line number in the originalLines the position of the first
     * char in the given line.
     * 
     * @param lineIndex
     * @param originalLines
     *            The original document (printed sequent)
     * @return
     */
    public static int getCharIndex(int lineIndex, String[] originalLines) {
        int charIndex = 0;
        for (int i = 0; i < originalLines.length; i++) {
            if (i == lineIndex) {
                return charIndex;
            }
            // add + 1 to count for the line-break at the end of each line that
            // doesn't appear in the split document (thanks to max)
            charIndex += originalLines[i].length() + 1;
        }

        throw new IndexOutOfBoundsException();
    }
}
