package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.parser.Location;
import org.jetbrains.annotations.Nullable;

import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author mattias ulbrich
 */
class ScriptLineParser {
    /**
     * Under this key, the command name is stored
     */
    public static final String COMMAND_KEY = "#1";
    public static final String LITERAL_KEY = "#literal";

    /**
     * This is the source of characters
     */
    private final Reader reader;
    private final ScriptLineLexer lexer = new ScriptLineLexer();
    /**
     * the filename from which the script is taken.
     */
    private String file;

    public ScriptLineParser(Reader reader) {
        this.reader = reader;
        this.file = null;
    }

    public ScriptLineParser(String filename) throws IOException {
        this.reader = new FileReader(filename);
        this.file = filename;
    }

    public @Nullable Map<String, String> getNextCommand() throws IOException, ScriptException {
        while (true) {
            int c = reader.read();
            if (c == -1) {
                if (lexer.state() != State.IN_ID) {
                    throw new ScriptException("Trailing characters at end of script (missing ';'?)",
                            file, getColumn(), getLine());
                } else {
                    return null;
                }
            }
            lexer.feed((char) c);
            Token lastToken = lexer.getLastToken();
            // ";" marks the terminates a command!
            if (lastToken != null && lastToken.type == TokenType.TERMINATE) {
                return assembleCommand(lexer.fetchAllAndClear());
            }
        }
    }

    private @Nullable Map<String, String> assembleCommand(List<Token> toks) {
        Map<String, String> result = new HashMap<>();
        String key = null;
        int impCounter = 1;
        int pos = 0;

        if (toks.size() <= 1) {
            return null;
        }

        do {
            Token cur = toks.get(pos), la = toks.get(pos + 1);
            if (la.type == TokenType.EQUAL) {
                // <cur> = <next>
                String next = pos + 2 <= toks.size() - 2 ? toks.get(pos + 2).text : "";
                result.put(cur.text, next);
                pos += 3; // three tokens consumed
            } else if (cur.type == TokenType.ID || cur.type == TokenType.STRING) {
                result.put("#" + (impCounter++), cur.text);
                pos++;
            }
            //else ignore token
        } while (pos < toks.size() - 1); // ignore last token (";")

        return result;
    }


    private void exc(int c) throws ScriptException {
        throw new ScriptException("Unexpected char '" + (char) c + "' at " + getLine() + ":" + getColumn(),
                file, getLine(), getColumn());
    }

    public int getLine() {
        return lexer.getLine();
    }

    public int getColumn() {
        return lexer.getColumn();
    }

    public int getPosition() {
        return getPosition();
    }

    public void setLocation(Location location) {
        lexer.line = location.getLine();
        lexer.col = location.getColumn();
        this.file = location.getFilename();
    }

}
