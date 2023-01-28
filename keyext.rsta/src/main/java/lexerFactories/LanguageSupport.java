package lexerFactories;

import lexerFactories.ANTLRLanguageSupportFactory;
import lexerFactories.JavaCCLanguageSupportFactory;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import org.fife.ui.rsyntaxtextarea.TokenMaker;

import javax.annotation.Nonnull;

public class LanguageSupport {
    public final SyntaxScheme syntaxScheme;
    public final TokenMaker tokenMaker;

    public LanguageSupport(@Nonnull SyntaxScheme syntaxScheme, @Nonnull TokenMaker tokenMaker) {
        if (tokenMaker == null || syntaxScheme == null) {
            throw new IllegalArgumentException();
        }
        this.tokenMaker = tokenMaker;
        this.syntaxScheme = syntaxScheme;
    }
}
