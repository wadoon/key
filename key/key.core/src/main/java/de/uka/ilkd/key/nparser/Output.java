package de.uka.ilkd.key.nparser;

public class Output {
    private static final int INDENT_STEP = 4;
    private static final String INDENT_BUFFER = " ".repeat(100);

    private final StringBuilder output;
    private int indentLevel = 0;
    private boolean isNewLine = true;

    public static String getIndent(int count) {
        // Substrings use a shared buffer
        return INDENT_BUFFER.substring(0, count);
    }

    public Output() {
        output = new StringBuilder();
    }

    private void indent() {
        output.append(getIndent(INDENT_STEP * indentLevel));
        this.isNewLine = false;
    }

    private void checkIndent() {
        if (this.isNewLine) {
            indent();
        }
    }

    public void space() {
        append(' ');
    }

    public void append(String value) {
        checkIndent();
        output.append(value);
    }

    public void append(char value) {
        checkIndent();
        output.append(value);
    }

    public void enterIndent() {
        indentLevel++;
    }

    public void exitIndent() {
        if (indentLevel == 0) {
            throw new IllegalStateException("Unmatched closing RPAREN.");
        }
        indentLevel--;
    }

    public boolean isNewLine() {
        return isNewLine;
    }

    public void newLineAndIndent() {
        if (!this.isNewLine) {
            output.append('\n');
        }
        indent();
    }

    public void newLine() {
        this.isNewLine = true;
        output.append('\n');
    }

    @Override
    public String toString() {
        return output.toString();
    }
}
