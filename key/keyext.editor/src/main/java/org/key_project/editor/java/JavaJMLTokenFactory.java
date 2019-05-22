package org.key_project.editor.java;

import edu.key_project.editor.java.JavaJMLLexer;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Lexer;
import org.fife.ui.rsyntaxtextarea.TokenTypes;

import java.util.HashMap;
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
        //JML
        add(TokenTypes.RESERVED_WORD_2, ENSURES, REQUIRES, MEASURED_BY, REPRESENTS,
                DECREASES,LOOP_DETERMINES, LOOP_INVARIANT, LOOP_SEPARATES,
                FORALL, EXISTS, NORMAL_BEHAVIOR, EXCEPTIONAL_BEHAVIOR, CONTINUE_BEHAVIOR, CONTINUES,
                INSTANCE, MODEL, DIVERGES, MEASURED_BY, ASSIGNABLE, ACCESSIBLE);


        add(TokenTypes.ERROR_CHAR, ERROR_CHAR);
        //JAVA
        add(TokenTypes.RESERVED_WORD,
                FINAL, ABSTRACT, PUBLIC, PRIVATE, PROTECTED, VOID,
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


        add(TokenTypes.WHITESPACE, WS, WS_CONTRACT);
    }

    public void add(Integer editorType, Integer... antlrTypes) {
        for (Integer antlrType : antlrTypes) {
            tokenMap.put(antlrType, editorType);
        }
    }

    @Override
    protected int rewriteTokenType(int antlrType) {
        return tokenMap.getOrDefault(antlrType, TokenTypes.WHITESPACE);
    }

    @Override
    protected Lexer createLexer(String toString) {
        return new JavaJMLLexer(CharStreams.fromString(toString));
    }
}
