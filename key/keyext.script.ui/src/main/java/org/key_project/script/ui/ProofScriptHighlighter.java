package org.key_project.script.ui;

import edu.kit.iti.formal.psdbg.parser.ScriptLexer;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Lexer;
import org.fife.ui.rsyntaxtextarea.Token;
import org.key_project.editor.java.Antlr4TokenMakerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (01.03.19)
 */
public class ProofScriptHighlighter extends Antlr4TokenMakerFactory {

    /*
        case ScriptLexer.MULTI_LINE_COMMENT:
            int commentStop = startOffset;
            for (; commentStop < end - 1; commentStop++) {
                if (array[commentStop] == '*' && array[commentStop + 1] == '/') {
                    break;
                }
            }
            addToken(text, startOffset, commentStop, ScriptLexer.MULTI_LINE_COMMENT,
                    newStartOffset);
            startOffset += 1 + commentStop;
            break;
        case ScriptLexer.STRING_LITERAL:
            int stringStop = startOffset;
            for (; stringStop < end; stringStop++) {
                if (array[stringStop] == '"') {
                    break;
                }
            }
            addToken(text, startOffset, stringStop, ScriptLexer.MULTI_LINE_COMMENT, newStartOffset);
            startOffset = 1 + stringStop;
            break;
        case ScriptLexer.TERM_LITERAL:
            int termStop = startOffset;
            for (; termStop < end; termStop++) {
                if (array[termStop] == '`') {
                    break;
                }
            }
            addToken(text, startOffset, termStop, ScriptLexer.MULTI_LINE_COMMENT, newStartOffset);
            startOffset = 1 + termStop;
            break;
    }
    */

    @Override
    protected Lexer createLexer(String toString) {
        return new ScriptLexer(CharStreams.fromString(toString));
    }

    @Override
    protected int rewriteTokenType(int type) {
        switch (type) {
            case ScriptLexer.AND:
            case ScriptLexer.OR:
            case ScriptLexer.IMP:
            case ScriptLexer.PLUS:
            case ScriptLexer.MINUS:
            case ScriptLexer.DIV:
            case ScriptLexer.EQ:
            case ScriptLexer.NEQ:
            case ScriptLexer.MUL:
            case ScriptLexer.COLON:
            case ScriptLexer.ASSIGN:
                return Token.OPERATOR;

            case ScriptLexer.FOREACH:
            case ScriptLexer.REPEAT:
            case ScriptLexer.WHILE:
            case ScriptLexer.IF:
            case ScriptLexer.CASE:
            case ScriptLexer.CASES:
            case ScriptLexer.DERIVABLE:
            case ScriptLexer.USING:
            case ScriptLexer.SCRIPT:
            case ScriptLexer.THEONLY:
            case ScriptLexer.CALL:
            case ScriptLexer.COMMA:
            case ScriptLexer.CLOSES:
            case ScriptLexer.STRICT:
                return Token.FUNCTION;
            case ScriptLexer.ID:
                return Token.IDENTIFIER;
            case ScriptLexer.WS:
                return Token.WHITESPACE;
            case ScriptLexer.MULTI_LINE_COMMENT:
            case ScriptLexer.SINGLE_LINE_COMMENT:
                return Token.COMMENT_MULTILINE;
            case ScriptLexer.TERM_LITERAL:
                return Token.LITERAL_BACKQUOTE;
            case ScriptLexer.STRING_LITERAL:
                return Token.LITERAL_STRING_DOUBLE_QUOTE;
            case ScriptLexer.DIGITS:
                return Token.LITERAL_NUMBER_DECIMAL_INT;
            case ScriptLexer.TRUE:
            case ScriptLexer.FALSE:
                return Token.LITERAL_BOOLEAN;
            case ScriptLexer.RBRACKET:
            case ScriptLexer.LBRACKET:
            case ScriptLexer.RPAREN:
            case ScriptLexer.LPAREN:
            case ScriptLexer.INDENT:
            case ScriptLexer.DEDENT:
                return Token.SEPARATOR;
            default:
                return 2;
        }
    }
}
