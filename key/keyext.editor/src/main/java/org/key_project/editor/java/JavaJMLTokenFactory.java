package org.key_project.editor.java;

import edu.key_project.editor.java.JavaJMLLexer;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.Recognizer;
import org.fife.ui.rsyntaxtextarea.Token;
import org.fife.ui.rsyntaxtextarea.TokenImpl;
import org.fife.ui.rsyntaxtextarea.TokenTypes;

import javax.swing.text.Segment;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static edu.key_project.editor.java.JavaJMLLexer.*;

/**
 * @author Alexander Weigl
 * @version 1 (22.05.19)
 */
public class JavaJMLTokenFactory extends Antlr4TokenMakerFactory {
    private Map<Integer, Integer> tokenMap = new HashMap<>();

    public JavaJMLTokenFactory() {
        add(TokenTypes.IDENTIFIER, IDENTIFIER);

        add(TokenTypes.MARKUP_COMMENT, JML_START, COMMENT_END);

        //JML
        add(TokenTypes.RESERVED_WORD_2, ENSURES, REQUIRES, MEASURED_BY, REPRESENTS,
                DECREASES, LOOP_DETERMINES, LOOP_INVARIANT, LOOP_SEPARATES, INVARIANT,
                CONSTRAINT, INITIALLY, AXIOM, BREAKS, CONTINUES, DECREASES, DEPENDS, DETERMINES,
                LOOP_DETERMINES, LOOP_SEPARATES, MODEL_METHOD_AXIOM, MERGE_PARAMS,
                REPRESENTS, REQUIRES, RETURNS, SEPARATES, SIGNALS, MODEL_BEHAVIOR, MODEL_METHOD_AXIOM,
                SIGNALS_ONLY, DIVERGES, SET, LOOP_INVARIANT, GHOST, INITIALLY,
                MODIFIABLE, MODIFIES, MEASURED_BY, NON_NULL, NULLABLE, RETURN_BEHAVIOR, BREAK_BEHAVIOR, PACKAGE,
                DEPENDS, MERGE_PARAMS, GHOST, MODIFIABLE, NON_NULL, NULLABLE, TWO_STATE, NO_STATE, NULLABLE_BY_DEFAULT,
                UNREACHABLE, PURE, STRICTLY_PURE, HELPER, NULLABLE_BY_DEFAULT,
                INSTANCE, TWO_STATE, NO_STATE, JC_NESTED_CONTRACT_START, JC_NESTED_CONTRACT_END, DOTDOT, SUCH_THAT,
                EQUIVALENCE, ANTIVALENCE, IMPLIES, IMPLIESBACKWARD, LOCKSET_LEQ,
                LOCKSET_LT, ST, SUCH_THAT, LBLPOS, LBLNEG, FORALL, IMPLEMENTS, MODIFIABLE, MODEL_METHOD_AXIOM,
                EXISTS, BY, DECLASSIFIES, ERASES, NEW_OBJECTS, SEMI_TOPLEVEL, LBLNEG, LBLPOS,
                SL_ALL, JE_MEASURED_BY, STOP, FORALL, EXISTS, NORMAL_BEHAVIOR, EXCEPTIONAL_BEHAVIOR, ERASES, NEW_OBJECTS,
                CONTINUE_BEHAVIOR, CONTINUES, INSTANCE, MODEL, DIVERGES, MEASURED_BY, ASSIGNABLE, ACCESSIBLE);


        add(TokenTypes.OPERATOR, BITOR, BITAND, AND, OR, NOTEQUAL, EQUAL, EQUIVALENCE, IMPLIES, IMPLIESBACKWARD,
                LOCKSET_LEQ, LOCKSET_LT, BANG, GT, LT, DIV, MOD, MUL, ADD, SUB, LE, LE, LT, GT, CARET, MOD, QUESTION,
                TILDE, COLON, ARROW, COLONCOLON);

        add(TokenTypes.WHITESPACE, WS_CONTRACT);

        add(TokenTypes.ERROR_CHAR, ERROR_CHAR);
        //JAVA
        add(TokenTypes.RESERVED_WORD, IMPORT, VOLATILE,
                FINAL, ABSTRACT, PUBLIC, PRIVATE, PROTECTED, VOID, INC, DEC,
                CLASS, INTERFACE, EXTENDS, IMPLEMENTS, BOOLEAN, ELSE, DEFAULT, SWITCH, CASE, RETURN,
                NULL_LITERAL, DO, IF, WHILE, FOR, TRY, CATCH, CONST, ASSERT, ENUM, IMPORT, INSTANCEOF, NATIVE,
                FINALLY, GOTO, NEW, STATIC, STRICTFP, SYNCHRONIZED, THIS, THROW, THROWS);

        //NULL_LITERAL
        add(TokenTypes.LITERAL_CHAR, CHAR_LITERAL);
        add(TokenTypes.LITERAL_BOOLEAN, BOOL_LITERAL);
        add(TokenTypes.LITERAL_BOOLEAN, BOOL_LITERAL);
        add(TokenTypes.LITERAL_NUMBER_DECIMAL_INT, DECIMAL_LITERAL, BINARY_LITERAL, OCT_LITERAL);
        add(TokenTypes.LITERAL_NUMBER_FLOAT, FLOAT_LITERAL, HEX_FLOAT_LITERAL);
        add(TokenTypes.LITERAL_NUMBER_HEXADECIMAL, HEX_LITERAL);
        add(TokenTypes.LITERAL_STRING_DOUBLE_QUOTE, STRING_LITERAL);

        add(TokenTypes.DATA_TYPE, INT, FLOAT, SHORT, BYTE, DOUBLE, LONG, CHAR, BOOLEAN);

        add(TokenTypes.COMMENT_MULTILINE, COMMENT_START, COMMENT_EVERY_CHAR, COMMENT_END);

        add(TokenTypes.WHITESPACE, WS, WS_CONTRACT);
    }

    public void add(Integer editorType, Integer... antlrTypes) {
        for (Integer antlrType : antlrTypes) {
            tokenMap.put(antlrType, editorType);
        }
    }

    @Override
    protected int rewriteTokenType(int antlrType) {
        return tokenMap.getOrDefault(antlrType, TokenTypes.ERROR_CHAR);
    }

    @Override
    protected Lexer createLexer(String toString) {
        return new JavaJMLLexer(CharStreams.fromString(toString));
    }


    @Override
    public Token getTokenList(Segment text, int initialTokenType, int startOffset) {
        resetTokenList();
        if (text == null) {
            throw new IllegalArgumentException();
        }

        String charSeq = text.toString();
        TokenImpl lastToken = null;

        boolean inComment = initialTokenType == TokenTypes.COMMENT_MULTILINE;
        boolean inJml = initialTokenType != TokenTypes.NULL && !inComment;

        Lexer lexer = createLexer(charSeq);
        if (inJml) lexer.pushMode(jmlContract);
        if (inComment) lexer.pushMode(comment);

        List<org.antlr.v4.runtime.Token> tokens = new ArrayList<>();
        org.antlr.v4.runtime.Token cur = lexer.nextToken();
        while (cur.getType() != Recognizer.EOF) {
            System.out.format("%25s %-25s%n", cur.getText(), lexer.getVocabulary().getSymbolicName(cur.getType()));

            tokens.add(cur);
            cur = lexer.nextToken();
        }


        if (tokens.isEmpty()) {
            addNullToken();
        } else {
            for (org.antlr.v4.runtime.Token token : tokens) {
                if (token.getType() == COMMENT_END) inJml = false;
                if (token.getType() == JML_START) inJml = true;
                if (token.getType() == COMMENT_START) inComment = true;
                if (token.getType() == COMMENT_END) inComment = false;

                int newType = rewriteTokenType(token.getType());
                int start = token.getStartIndex();
                TokenImpl t = new TokenImpl(text,
                        text.offset + start,
                        text.offset + start + token.getText().length() - 1,
                        startOffset + start, newType, 0);
                t.setLanguageIndex(inJml ? 1 : 0);
                if (firstToken == null) {
                    firstToken = t;
                } else {
                    assert lastToken != null;
                    lastToken.setNextToken(t);
                }
                lastToken = t;
            }
            if (!inJml && inComment) {
                TokenImpl token = new TokenImpl();
                token.text = null;
                token.setType(Token.NULL);
                token.setOffset(-1);
                token.setNextToken(null);
                lastToken.setNextToken(token);//close line with a "0" if not ended in JML mode.
            }
        }

        return firstToken;
    }
}
