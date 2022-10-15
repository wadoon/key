package rsta;

import antlr.ANTLRLexerFactory;
import antlr.ANTLRTokenMaker;
import javacc.JavaCCLexerFactory;
import javacc.JavaCCTokenMaker;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import org.fife.ui.rsyntaxtextarea.TokenMaker;

import javax.annotation.Nonnull;

public class LanguageSupport {
    public final SyntaxScheme syntaxScheme;
    public final TokenMaker tokenMaker;

    public LanguageSupport(@Nonnull SyntaxScheme syntaxScheme, @Nonnull ANTLRLexerFactory factory) {
        this(syntaxScheme, new ANTLRTokenMaker(factory));
    }

    public LanguageSupport(@Nonnull SyntaxScheme syntaxScheme, @Nonnull JavaCCLexerFactory factory) {
        this(syntaxScheme, new JavaCCTokenMaker(factory));
    }

    public LanguageSupport(@Nonnull SyntaxScheme syntaxScheme, @Nonnull TokenMaker tokenMaker) {
        if (tokenMaker == null || syntaxScheme == null) {
            throw new IllegalArgumentException();
        }
        this.tokenMaker = tokenMaker;
        this.syntaxScheme = syntaxScheme;
    }
}
