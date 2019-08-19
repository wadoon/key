package org.key_project.script.ui;

import edu.kit.iti.formal.psdbg.parser.ScriptLexer;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.Lexer;
import org.fife.ui.rsyntaxtextarea.Token;
import org.key_project.editor.java.JavaJMLTokenFactory;

/**
 * @author Alexander Weigl
 * @version 1 (01.03.19)
 */
public class ProofScriptHighlighter extends JavaJMLTokenFactory {
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
            case ScriptLexer.BIND:
            case ScriptLexer.MATCH:
            case ScriptLexer.SCRIPT:
            case ScriptLexer.THEONLY:
            case ScriptLexer.CALL:
            case ScriptLexer.COMMA:
            case ScriptLexer.CLOSES:
            case ScriptLexer.STRICT:
            case ScriptLexer.DEFAULT:
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
            case ScriptLexer.STRING_LITERAL_DOUBLE:
            case ScriptLexer.STRING_LITERAL_SINGLE:
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
            case ScriptLexer.SEMICOLON:
                return Token.SEPARATOR;
            case ScriptLexer.ERROR_CHAR:
                return Token.ERROR_CHAR;
            default:
                return Token.ERROR_IDENTIFIER;
        }
    }

    @Override
    protected int simulateNewLine(Lexer l) {
        return l._mode;
    }

    @Override
    protected void changeType(Lexer lexer, org.antlr.v4.runtime.Token cur) {
        ScriptLexer l = (ScriptLexer) lexer;
        CommonToken tok = (CommonToken) cur;
        switch (l._mode) {
            case ScriptLexer.STRINGS:
                tok.setType(ScriptLexer.STRING_LITERAL_SINGLE);
                break;
            case ScriptLexer.STRINGD:
                tok.setType(ScriptLexer.STRING_LITERAL_DOUBLE);
                break;
            case ScriptLexer.TERM:
                tok.setType(ScriptLexer.TERM_LITERAL);
                break;
            case ScriptLexer.COMMENT:
                tok.setType(ScriptLexer.MULTI_LINE_COMMENT);
                break;
        }
    }
}
