package rsta;

import antlr.ANTLRLexerFactory;
import javacc.JavaCCLexerFactory;
import javacc.PositionStream;
import javacc.SimpleCharStream;
import javacc.TokenManager;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.misc.Nullable;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;

import java.io.StringReader;
import java.lang.reflect.InvocationTargetException;

public class InputDisplay {

    public static void display(String text, String grammarName) {
        TextEditor textEditor = new TextEditor();

        textEditor.addPanel(text.toString(), createLanguageSupport(grammarName));

        textEditor.setVisible(true);
    }

    private static @Nullable LanguageSupport createLanguageSupport(String grammarName) {
        if (grammarName.endsWith(".g4")) {
            return createANTLRSupport("antlr." + grammarName.substring(0, grammarName.length() - 3));
        } else if (grammarName.endsWith(".jj")) {
            return createJavaCCSupport("javacc." + grammarName.substring(0, grammarName.length() - 3));
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

    private static @Nullable LanguageSupport createANTLRSupport(String grammarName) {
        SyntaxScheme scheme = createSyntaxScheme(grammarName);
        try {
            Class<Lexer> lexerClass
                    = (Class<Lexer>) Class.forName(grammarName + "Lexer");
            ANTLRLexerFactory factory = new ANTLRLexerFactory() {
                @Override
                public Lexer create(String input) {
                    try {
                        return lexerClass
                                .getConstructor(CharStream.class)
                                .newInstance(new ANTLRInputStream(input));
                    } catch (InvocationTargetException | InstantiationException
                             | IllegalAccessException | NoSuchMethodException e) {
                        e.printStackTrace();
                    }
                    return null;
                }
            };
            return new LanguageSupport(scheme, factory);
        } catch (ClassNotFoundException e) {
            e.printStackTrace();
        }
        return null;
    }

    private static SyntaxScheme createSyntaxScheme(String grammarName) {
        try {
            Class<SyntaxScheme> syntaxSchemeClass
                    = (Class<SyntaxScheme>) Class.forName(grammarName + "SyntaxScheme");
            SyntaxScheme scheme = syntaxSchemeClass.getConstructor().newInstance();
            return scheme;
        } catch (ClassNotFoundException | NoSuchMethodException | InstantiationException |
                 IllegalAccessException | InvocationTargetException e) {
            e.printStackTrace();
        }
        return null;
    }

}
