package rsta;

import lexerFacade.LexerTokenMaker;
import lexerFacade.MultipleLexersLexer;
import lexerFactories.*;
import org.antlr.v4.runtime.Lexer;
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.annotation.Nullable;
import javax.swing.*;
import java.awt.*;
import java.lang.reflect.InvocationTargetException;
import java.util.*;
import java.util.List;
import java.util.stream.Collectors;

public class InputDisplay {

    private static final Class<Lexer> antlrLexerClass = Lexer.class;

    public static TextEditor display(String text,
                                     Dialog parent,
                                     List<Class<?>> lexerClasses,
                                     Map<Class<?>, Map<String, Class<?>>> map) {
        TextEditor textEditor = new TextEditor(parent);

        LanguageSupport languageSupport = createLanguageSupport(lexerClasses, map);

        if(languageSupport != null) {
            textEditor.addPanel(text.toString(), languageSupport);
        }

        return textEditor;
    }

    private static @Nullable LanguageSupport createLanguageSupport(
            List<Class<?>> lexerClasses,
            Map<Class<?>, Map<String, Class<?>>> map) {
        Map<LanguageSupportFactory, Map<String, LanguageSupportFactory>> delMap
                = new HashMap<>();
        for (Map.Entry<Class<?>, Map<String, Class<?>>> entry: map.entrySet()) {
            Map<String, LanguageSupportFactory> tokenMap = new HashMap<>();
            for (Map.Entry<String, Class<?>> tokenTypeMap: entry.getValue().entrySet()) {
                tokenMap.put(tokenTypeMap.getKey(), getFactoryForLexerClasses(
                        new MultipleLexersLexer.LexerDelegationMap(new HashMap<>()),
                        Collections.singletonList(tokenTypeMap.getValue())));
            }
            delMap.put(
                    getFactoryForLexerClasses(
                            new MultipleLexersLexer.LexerDelegationMap(new HashMap<>()),
                            Collections.singletonList(entry.getKey())),
                    tokenMap);
        }
        MultipleLexersLexer.LexerDelegationMap delegationMap
                = new MultipleLexersLexer.LexerDelegationMap(delMap);
        LanguageSupportFactory factory = getFactoryForLexerClasses(delegationMap, lexerClasses);
        if (factory == null) {
            return null;
        }
        return new LanguageSupport(factory.getSyntaxScheme(), new LexerTokenMaker(factory));
    }

    private static @Nullable LanguageSupportFactory getFactoryForLexerClasses(
            MultipleLexersLexer.LexerDelegationMap delegationMap,
            List<Class<?>> lexerClasses) {
        if (lexerClasses.size() == 0) {
            return null;
        }
        if (lexerClasses.size() > 1) {
            return new VariousGrammarsSyntaxSchemeFactory(
                    lexerClasses.stream()
                            .map(clazz
                                    -> getFactoryForLexerClasses(
                                            new MultipleLexersLexer.LexerDelegationMap(
                                                    new HashMap<>()), Collections.singletonList(clazz)))
                            .collect(Collectors.toList()),
                    delegationMap);
        }
        Class<?> lexerClass = lexerClasses.get(0);
        LanguageSupportFactory factory = null;
        if (lexerClass != null && antlrLexerClass.isAssignableFrom(lexerClass)) {
            factory = createANTLRSupport((Class<Lexer>) lexerClass);
        } else if (lexerClass != null && lexerFacade.Lexer.class.isAssignableFrom(lexerClass)){
            try {
                factory = createJavaCCSupport((Class<lexerFacade.Lexer>) lexerClass);
            } catch (IllegalArgumentException e) {
                return null;
            }
        }
        return factory;
    }

    private static @Nullable LanguageSupportFactory createJavaCCSupport(Class<? extends lexerFacade.Lexer> tokenMgrClass) {
        return new JavaCCLanguageSupportFactory(tokenMgrClass);
    }

    private static @Nullable LanguageSupportFactory createANTLRSupport(Class<Lexer> lexerClass) {
        return new ANTLRLanguageSupportFactory(lexerClass);
    }

    public static Component panel(String text, List<Class<?>> lexerClasses, Map<Class<?>, Map<String, Class<?>>> map, Dialog parent) {
        LanguageSupport lang = createLanguageSupport(lexerClasses, map);
        RSyntaxTextArea textArea = new RSyntaxTextArea();
        RSyntaxDocument doc = (RSyntaxDocument) textArea.getDocument();
        if (lang != null) {
            // Set the syntax scheme which defines how to display different types of tokens.
            textArea.setSyntaxScheme(lang.syntaxScheme);
            // Set the token maker used to create RSTA tokens out of the input stream.
            doc.setSyntaxStyle(lang.tokenMaker);
        }

        textArea.setText(text);
        textArea.setEditable(false);

        return new RTextScrollPane(textArea);
    }
}
