package rsta;

import lexerFacade.LexerTokenMaker;
import lexerFactories.ANTLRLanguageSupportFactory;
import lexerFactories.JavaCCLanguageSupportFactory;
import lexerFactories.LanguageSupport;
import lexerFactories.LanguageSupportFactory;
import org.antlr.v4.runtime.Lexer;
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.annotation.Nullable;
import java.awt.*;
import java.lang.reflect.InvocationTargetException;

public class InputDisplay {

    private static final Class<Lexer> antlrLexerClass = Lexer.class;

    public static TextEditor display(String text, Class<?> lexerClass, Dialog parent) {
        TextEditor textEditor = new TextEditor(parent);

        LanguageSupport languageSupport = createLanguageSupport(lexerClass);

        if(languageSupport != null) {
            textEditor.addPanel(text.toString(), languageSupport);
        }

        return textEditor;
    }

    private static @Nullable LanguageSupport createLanguageSupport(Class<?> lexerClass) {
        LanguageSupportFactory factory;
        if (antlrLexerClass.isAssignableFrom(lexerClass)) {
            factory = createANTLRSupport((Class<Lexer>) lexerClass);
        } else {
            factory = createJavaCCSupport(lexerClass);
        }
        return new LanguageSupport(factory.getSyntaxScheme(), new LexerTokenMaker(factory));
    }

    private static SyntaxScheme createSyntaxScheme(String grammarName) {
        try {
            Class<SyntaxScheme> syntaxSchemeClass
                    = (Class<SyntaxScheme>) Class.forName(grammarName + "SyntaxScheme");
            return syntaxSchemeClass.getConstructor().newInstance();
        } catch (ClassNotFoundException | NoSuchMethodException | InstantiationException |
                 IllegalAccessException | InvocationTargetException e) {
            e.printStackTrace();
        }
        return null;
    }

    private static @Nullable LanguageSupportFactory createJavaCCSupport(Class<?> tokenMgrClass) {
        return new JavaCCLanguageSupportFactory(tokenMgrClass);
    }

    private static @Nullable LanguageSupportFactory createANTLRSupport(Class<Lexer> lexerClass) {
        return new ANTLRLanguageSupportFactory(lexerClass);
    }

    public static Component panel(String text, Class<?> lexerClass, Dialog parent) {
        LanguageSupport lang = createLanguageSupport(lexerClass);
        RSyntaxTextArea textArea = new RSyntaxTextArea();
        RSyntaxDocument doc = (RSyntaxDocument) textArea.getDocument();
        // Set the syntax scheme which defines how to display different types of tokens.
        textArea.setSyntaxScheme(lang.syntaxScheme);
        // Set the token maker used to create RSTA tokens out of the input stream.
        doc.setSyntaxStyle(lang.tokenMaker);

        textArea.setText(text);
        textArea.setEditable(false);

        RTextScrollPane sp = new RTextScrollPane(textArea);
        return sp;
    }
}
