package rsta;

import antlr.ANTLRLexerFactory;
import javacc.JavaCCLexerFactory;
import javacc.PositionStream;
import javacc.SimpleCharStream;
import javacc.TokenManager;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.Parser;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.awt.*;
import java.io.StringReader;
import java.lang.reflect.InvocationTargetException;
import java.util.Optional;

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
        if (antlrLexerClass.isAssignableFrom(lexerClass)) {
            return createANTLRSupport((Class<Lexer>) lexerClass);
        }
        return null;
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

    private static @Nullable LanguageSupport createJavaCCSupport(String grammarName) {
        SyntaxScheme scheme = createSyntaxScheme(grammarName);
        try {
            Class<TokenManager> tokenMgrClass
                    = (Class<TokenManager>) Class.forName(grammarName + "TokenManager");
            JavaCCLexerFactory factory = new JavaCCLexerFactory() {
                @Override
                public PositionStream createStream(String input) {
                    return new SimpleCharStream(new StringReader(input), 0, 0);
                }

                @Override
                public TokenManager create(PositionStream stream) {
                    try {
                        return tokenMgrClass.getConstructor(SimpleCharStream.class).newInstance(stream);
                    } catch (NoSuchMethodException | InstantiationException |
                             IllegalAccessException | InvocationTargetException e) {
                        e.printStackTrace();
                        return null;
                    }
                }
            };
            return new LanguageSupport(scheme, factory);
        } catch (ClassNotFoundException e) {
            e.printStackTrace();
        }
        return null;
    }

    private static @Nullable LanguageSupport createANTLRSupport(Class<Lexer> lexerClass) {
        SyntaxScheme scheme;
        try {
            String antlrGrammarFileName
                    = "antlr." + makeLexer(lexerClass, "").getGrammarFileName();
            scheme = createSyntaxScheme(
                    antlrGrammarFileName.substring(0, antlrGrammarFileName.length() - 3)
            );
        } catch (NoSuchMethodException | InvocationTargetException
                 | InstantiationException | IllegalAccessException e) {
            e.printStackTrace();
            return null;
        }
        ANTLRLexerFactory factory = new ANTLRLexerFactory() {
            @Override
            public Lexer create(String input) {
                try {
                    return makeLexer(lexerClass, input);
                } catch (NoSuchMethodException | InvocationTargetException |
                         InstantiationException | IllegalAccessException e) {
                    e.printStackTrace();
                }
                return null;
            }
        };
        return new LanguageSupport(scheme, factory);
    }

    private static Lexer makeLexer(Class<Lexer> lexerClass, String input)
            throws NoSuchMethodException, InvocationTargetException,
            InstantiationException, IllegalAccessException {
        return lexerClass
                    .getConstructor(CharStream.class)
                    .newInstance(new ANTLRInputStream(input));
    }

}
