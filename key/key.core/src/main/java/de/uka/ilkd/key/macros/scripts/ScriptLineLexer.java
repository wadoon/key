package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.parser.Location;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

/**
 * The state of the regular expression parser.
 */
enum State {
    /* initial, between arguments, between commands */
    INIT,
    /* within an identifier */
    IN_ID,

    IN_DQUOTE,
    IN_SQUOTE,

    /* within a (single line) comment */
    IN_COMMENT;
}

enum TokenType {ID, STRING, EQUAL, TERMINATE}

class Token {
    public TokenType type;
    public String text;
    int line, col, pos;
}

/**
 * @author Alexander Weigl
 * @version 1 (11.07.19)
 */
public class ScriptLineLexer {
    private static final String ADMISSIBLE_CHARS = "-_$@";
    private final Stack<State> state = new Stack<>();
    /**
     * current column number
     */
    int col;
    /**
     * current line number
     */
    int line = 1;
    private int nextTokenToFetch = 0;
    /**
     *
     */
    private int pos = 0;
    /**
     * the filename from which the script is taken.
     */
    private String file;
    /**
     * number of characters read so far
     */
    private int readChars;
    /**
     * While within a string literal, this stores the character with which the
     * string has started.
     */
    private int stringInitChar;
    private StringBuilder storedChars = new StringBuilder();
    private List<Token> publishedTokens = new LinkedList<>();

    public ScriptLineLexer() {
        state.add(State.INIT);
    }

    public void feed(char c) {
        State state = this.state.peek();

        if (c == '\n') {
            ++line;
            col = 0;
        } else {
            ++col;
        }
        ++pos;

        switch (state) {
            case INIT:
                if (isIDChar(c)) {
                    nextState(State.IN_ID);
                    saveChar(c, true);
                } else {
                    switch (c) {
                        case '"':
                            nextState(State.IN_DQUOTE);
                            break;
                        case '\'':
                            nextState(State.IN_SQUOTE);
                            break;
                        case '#':
                            nextState(State.IN_COMMENT);
                            break;
                        case '=':
                            publishToken(TokenType.EQUAL, "=");
                            break;
                        case ';':
                            publishToken(TokenType.TERMINATE, ";");
                            break;
                    }
                }
                break;
            case IN_ID:
                //IN_ID waiting for SPACE
                if (isIDChar(c)) {
                    saveChar(c, false);
                } else if (Character.isSpaceChar(c)) {
                    publishToken(TokenType.ID);
                    nextState(State.INIT);
                } else if (c == ';' || c == '=' || c == '"' || c == '\'') {
                    publishToken(TokenType.ID);
                    nextState(State.INIT);
                    feed(c);
                }
                break;
            case IN_DQUOTE:
                if (c != '"') {
                    saveChar(c, false);
                } else {
                    publishToken(TokenType.STRING);
                    nextState(State.INIT);
                }
                break;
            case IN_SQUOTE:
                if (c != '\'') {
                    saveChar(c, false);
                } else {
                    publishToken(TokenType.STRING);
                    nextState(State.INIT);
                }
                break;
            case IN_COMMENT:
                if (c == '\n') nextState(State.INIT);
                break;
        }
    }

    private void publishToken(TokenType type, String value) {
        Token token = new Token();
        token.text = value;
        token.type = type;
        token.col = col;
        token.line = line;
        token.pos = pos;
        publishedTokens.add(token);
    }

    private void publishToken(TokenType type) {
        publishToken(type, storedChars.toString());
        storedChars.setLength(0);
    }

    private void saveChar(char c) {
        saveChar(c, false);
    }

    private void saveChar(char c, boolean clear) {
        if (clear) storedChars.setLength(0);
        storedChars.append(c);
    }

    private void nextState(State s) {
        popState();
        pushState(s);
    }

    private void pushState(State s) {
        state.push(s);
    }

    private void popState() {
        state.pop();
    }

    public int getLine() {
        return line;
    }

    public int getColumn() {
        return col;
    }

    public int getPosition() {
        return pos;
    }

    public void setLocation(Location location) {
        this.line = location.getLine();
        this.col = location.getColumn();
        this.file = location.getFilename();
    }

    public State state() {
        return state.peek();
    }

    public @NotNull List<Token> fetchAllAndClear() {
        List<Token> toks = new ArrayList<>(publishedTokens);
        publishedTokens.clear();
        return toks;
    }

    public @Nullable Token fetchToken() {
        if (publishedTokens.size() > nextTokenToFetch) {
            return publishedTokens.get(nextTokenToFetch++);
        }
        return null;
    }

    public @Nullable Token getLastToken() {
        if (publishedTokens.size() > 0) {
            return publishedTokens.get(publishedTokens.size() - 1);
        } else {
            return null;
        }
    }

    private boolean isIDChar(int c) {
        return Character.isLetterOrDigit(c) || ADMISSIBLE_CHARS.indexOf((char) c) > -1;
    }
}
