package de.uka.ilkd.key.proof.mgt.deps;

import java.util.Iterator;

/**
 * An iterator for dependency file tokens
 */
public class DepFileTokenizer implements Iterator<DepFileTokenizer.Token> {
    /**
     * Input to tokenize
     */
    private final String input;
    /**
     * Current index in the input
     */
    private int idx = 0;
    /**
     * Position in the input as line and column
     */
    private Pos pos = new Pos(1, 0);

    public DepFileTokenizer(String input) {
        this.input = input;
    }

    @Override
    public boolean hasNext() {
        return idx < input.length();
    }

    @Override
    public Token next() {
        if (!hasNext()) return null;

        char c = getCurrent();
        if (Character.isWhitespace(c)) {
            eat();
            return next();
        }

        TokenType tt = TokenType.UNKNOWN;
        switch (c) {
            case '#': {
                eatUntilNewLine();
                return next();
            }
            case '{': {
                tt = TokenType.L_BRACE;
                break;
            }
            case '}': {
                tt = TokenType.R_BRACE;
                break;
            }
            case ',': {
                tt = TokenType.COMMA;
                break;
            }
            case ':': {
                tt = TokenType.COLON;
                break;
            }
            case '|': {
                tt = TokenType.VERT_DASH;
                break;
            }
            case '/': {
                // File path
                Pos start = pos;
                int startIdx = idx;

                eatUntilEndOfFilepath();

                String spelling = input.substring(startIdx, idx).trim();
                return new Token(TokenType.FILE_PATH, spelling, start);
            }
            default: {
                if (c == '-' || Character.isLetterOrDigit(c)) {
                    // Hash or contract name
                    Pos start = pos;
                    int startIdx = idx;

                    eatUntilNonNameOrHash();

                    String spelling = input.substring(startIdx, idx).trim();
                    try {
                        Integer.parseInt(spelling);
                        return new Token(TokenType.NUMBER, spelling, start);
                    } catch (NumberFormatException e) {
                        return new Token(TokenType.CONTRACT_NAME, spelling, start);
                    }
                }
            }
        }

        Token t = new Token(tt, "" + c, pos);
        idx++;
        pos = pos.advance();
        return t;
    }

    /**
     * @return Current character
     */
    private char getCurrent() {
        return input.charAt(idx);
    }

    /**
     * Advance position in the input
     */
    private void eat() {
        boolean isNewLine = getCurrent() == '\n';
        idx++;
        if (isNewLine) {
            pos = pos.newLine();
        } else {
            pos = pos.advance();
        }
    }

    /**
     * Advance till line is over
     */
    private void eatUntilNewLine() {
        while (getCurrent() != '\n') {
            eat();
        }
        eat();
    }

    /**
     * Advance to end of hash or contract name
     */
    private void eatUntilNonNameOrHash() {
        while (getCurrent() != '|' && getCurrent() != '{' && getCurrent() != '\n') {
            eat();
        }
    }

    /**
     * Advance to end of path
     */
    private void eatUntilEndOfFilepath() {
        while (getCurrent() != '{' || (idx + 1 < input.length() && input.charAt(idx + 1) != '\n')) {
            eat();
        }
    }

    /**
     * A token in the dependency file
     */
    static class Token {
        /**
         * Type of token
         */
       private final TokenType type;
        /**
         * Original spelling in the source
         */
       private final String spelling;
        /**
         * Start position in source
         */
       private final Pos srcPos;

        public Token(TokenType type, String spelling, Pos srcPos) {
            this.type = type;
            this.spelling = spelling;
            this.srcPos = srcPos;
        }

        public TokenType getType() {
            return type;
        }

        public String getSpelling() {
            return spelling;
        }

        public Pos getSrcPos() {
            return srcPos;
        }

        @Override
        public String toString() {
            return spelling + "@" + srcPos;
        }
    }

    /**
     * Type of tokens
     */
    enum TokenType {
        L_BRACE,
        R_BRACE,
        COMMA,
        COLON,
        VERT_DASH,
        NUMBER,
        FILE_PATH,
        CONTRACT_NAME,
        UNKNOWN;

        @Override
        public String toString() {
            switch (this) {
                case L_BRACE:
                    return "{";
                case R_BRACE:
                    return "}";
                case COMMA:
                    return ",";
                case COLON:
                    return ":";
                case VERT_DASH:
                    return "|";
                case NUMBER:
                    return "<number>";
                case FILE_PATH:
                    return "<file-name>";
                case CONTRACT_NAME:
                    return "<contract-name>";
                default:
                    return "<unknown>";
            }
        }
    }

    /**
     * Position in the source file as line and column
     */
    static class Pos {
        private final int line;
        private final int column;

        public Pos(int line, int column) {
            this.line = line;
            this.column = column;
        }

        public int getLine() {
            return line;
        }

        public int getColumn() {
            return column;
        }

        /**
         * @return Next position in the same line
         */
        public Pos advance() {
            return advance(1);
        }

        /**
         * @param columns How many columns to advance
         * @return Position after <code>columns</code> many columns
         */
        public Pos advance(int columns) {
            return new Pos(line, column + columns);
        }

        /**
         * @return Start position in the next line
         */
        public Pos newLine() {
            return new Pos(line + 1, 0);
        }

        @Override
        public String toString() {
            return "" + line + ":" + column;
        }
    }
}
