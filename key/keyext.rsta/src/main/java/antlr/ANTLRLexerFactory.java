package antlr;

import org.antlr.v4.runtime.Lexer;

public interface ANTLRLexerFactory {

    Lexer create(String input);
}
