package rsta;

import antlr.ANTLRLexerFactory;
import antlr.ANTLRTokenMaker;
import javacc.JavaCCLexerFactory;
import javacc.JavaCCTokenMaker;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import org.fife.ui.rsyntaxtextarea.TokenMaker;

public class LanguageSupport {
    public final SyntaxScheme syntaxScheme;
    public final TokenMaker tokenMaker;

    public LanguageSupport(SyntaxScheme syntaxScheme, ANTLRLexerFactory factory) {
        this(syntaxScheme, new ANTLRTokenMaker(factory));
    }

    public LanguageSupport(SyntaxScheme syntaxScheme, JavaCCLexerFactory factory) {
        this(syntaxScheme, new JavaCCTokenMaker(factory));
    }

    public LanguageSupport(SyntaxScheme syntaxScheme, TokenMaker tokenMaker) {
        this.tokenMaker = tokenMaker;
        this.syntaxScheme = syntaxScheme;
    }
}
