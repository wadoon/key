package edu.key_project.script.ui;

import edu.kit.iti.formal.psdbg.parser.ScriptLanguageLexer;
import org.antlr.v4.runtime.CharStreams;
import org.fife.ui.rsyntaxtextarea.AbstractTokenMaker;
import org.fife.ui.rsyntaxtextarea.Token;
import org.fife.ui.rsyntaxtextarea.TokenMap;

import javax.swing.text.Segment;

/**
 * @author Alexander Weigl
 * @version 1 (01.03.19)
 */
public class ProofScriptHighlighter extends AbstractTokenMaker {

    /*
        case ScriptLanguageLexer.MULTI_LINE_COMMENT:
            int commentStop = startOffset;
            for (; commentStop < end - 1; commentStop++) {
                if (array[commentStop] == '*' && array[commentStop + 1] == '/') {
                    break;
                }
            }
            addToken(text, startOffset, commentStop, ScriptLanguageLexer.MULTI_LINE_COMMENT,
                    newStartOffset);
            startOffset += 1 + commentStop;
            break;
        case ScriptLanguageLexer.STRING_LITERAL:
            int stringStop = startOffset;
            for (; stringStop < end; stringStop++) {
                if (array[stringStop] == '"') {
                    break;
                }
            }
            addToken(text, startOffset, stringStop, ScriptLanguageLexer.MULTI_LINE_COMMENT, newStartOffset);
            startOffset = 1 + stringStop;
            break;
        case ScriptLanguageLexer.TERM_LITERAL:
            int termStop = startOffset;
            for (; termStop < end; termStop++) {
                if (array[termStop] == '`') {
                    break;
                }
            }
            addToken(text, startOffset, termStop, ScriptLanguageLexer.MULTI_LINE_COMMENT, newStartOffset);
            startOffset = 1 + termStop;
            break;
    }
    */

    @Override
    public TokenMap getWordsToHighlight() {
        TokenMap tokenMap = new TokenMap();
        String[] words = new String[]{"cases", "case", "try", "closes", "derivable", "default",
                "using", "match", "script", "true", "false", "call", "repeat", "foreach",
                "theonly", "strict", "relax", "while", "if"};
        for (String word : words) {
            tokenMap.put(word, Token.RESERVED_WORD);
        }
        return tokenMap;
    }

    @Override
    public void addToken(Segment segment, int start, int end, int tokenType, int startOffset) {
        // This assumes all keywords, etc. were parsed as "identifiers."
        if (tokenType == Token.IDENTIFIER) {
            int value = wordsToHighlight.get(segment, start, end);
            if (value != -1) {
                tokenType = value;
            }
        }
        super.addToken(segment, start, end, tokenType, startOffset);
    }

    @Override
    public Token getTokenList(Segment text, int initialTokenType, int startOffset) {
        resetTokenList();
        char[] array = text.array;
        int offset = text.offset;
        int count = text.count;
        int end = offset + count;

        // Token starting offsets are always of the form:
        // 'startOffset + (currentTokenStart-offset)', but since startOffset and
        // offset are constant, tokens' starting positions become:
        // 'newStartOffset+currentTokenStart'.
        int newStartOffset = startOffset - offset;

        String input = text.toString();
        ScriptLanguageLexer lexer = new ScriptLanguageLexer(CharStreams.fromString(input));

        for (org.antlr.v4.runtime.Token t = lexer.nextToken();
             t.getType() != -1; t = lexer.nextToken()) {
            int start = t.getStartIndex() + offset;
            addToken(array, start, offset + t.getStopIndex(), visualStyle(t.getType()), startOffset + t.getStartIndex());
        }

        // Return the first token in our linked list.
        if (firstToken == null)
            addNullToken();
        return firstToken;

    }

    private int visualStyle(int type) {
        switch (type) {
            case ScriptLanguageLexer.AND:
            case ScriptLanguageLexer.OR:
            case ScriptLanguageLexer.IMP:
            case ScriptLanguageLexer.PLUS:
            case ScriptLanguageLexer.MINUS:
            case ScriptLanguageLexer.DIV:
            case ScriptLanguageLexer.EQ:
            case ScriptLanguageLexer.NEQ:
            case ScriptLanguageLexer.MUL:
            case ScriptLanguageLexer.COLON:
            case ScriptLanguageLexer.ASSIGN:
                return Token.OPERATOR;

            case ScriptLanguageLexer.FOREACH:
            case ScriptLanguageLexer.REPEAT:
            case ScriptLanguageLexer.WHILE:
            case ScriptLanguageLexer.IF:
            case ScriptLanguageLexer.CASE:
            case ScriptLanguageLexer.CASES:
            case ScriptLanguageLexer.DERIVABLE:
            case ScriptLanguageLexer.USING:
            case ScriptLanguageLexer.SCRIPT:
            case ScriptLanguageLexer.THEONLY:
            case ScriptLanguageLexer.CALL:
            case ScriptLanguageLexer.COMMA:
            case ScriptLanguageLexer.CLOSES:
            case ScriptLanguageLexer.STRICT:
                return Token.FUNCTION;
            case ScriptLanguageLexer.ID:
                return Token.IDENTIFIER;
            case ScriptLanguageLexer.WS:
                return Token.WHITESPACE;
            case ScriptLanguageLexer.MULTI_LINE_COMMENT:
            case ScriptLanguageLexer.SINGLE_LINE_COMMENT:
                return Token.COMMENT_MULTILINE;
            case ScriptLanguageLexer.TERM_LITERAL:
                return Token.LITERAL_BACKQUOTE;
            case ScriptLanguageLexer.STRING_LITERAL:
                return Token.LITERAL_STRING_DOUBLE_QUOTE;
            case ScriptLanguageLexer.DIGITS:
                return Token.LITERAL_NUMBER_DECIMAL_INT;
            case ScriptLanguageLexer.TRUE:
            case ScriptLanguageLexer.FALSE:
                return Token.LITERAL_BOOLEAN;
            case ScriptLanguageLexer.RBRACKET:
            case ScriptLanguageLexer.LBRACKET:
            case ScriptLanguageLexer.RPAREN:
            case ScriptLanguageLexer.LPAREN:
            case ScriptLanguageLexer.INDENT:
            case ScriptLanguageLexer.DEDENT:
                return Token.SEPARATOR;
            default:
                return 2;
        }
    }
}
