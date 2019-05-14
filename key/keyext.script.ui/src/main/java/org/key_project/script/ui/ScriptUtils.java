package org.key_project.script.ui;

import de.uka.ilkd.key.api.KeYApi;
import lombok.NonNull;
import org.fife.ui.autocomplete.AutoCompletion;
import org.fife.ui.autocomplete.BasicCompletion;
import org.fife.ui.autocomplete.CompletionProvider;
import org.fife.ui.autocomplete.DefaultCompletionProvider;
import org.fife.ui.rsyntaxtextarea.AbstractTokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.CodeTemplateManager;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.TokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.folding.CurlyFoldParser;
import org.fife.ui.rsyntaxtextarea.folding.FoldParserManager;
import org.fife.ui.rsyntaxtextarea.templates.CodeTemplate;
import org.fife.ui.rsyntaxtextarea.templates.StaticCodeTemplate;
import org.key_project.util.java.IOUtil;

import java.io.IOException;
import java.net.URL;
import java.util.Arrays;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (02.03.19)
 */
public class ScriptUtils {
    public static final String KPS_LANGUAGE_ID = "text/kps";

    public static boolean isCommented(@NonNull String text) {
        text = text.trim();
        String[] lines = text.split("\n");
        return Arrays.stream(lines).allMatch(l -> l.trim().startsWith("//"));
    }

    public static String removeComments(@NonNull String text) {
        Pattern leadingComment = Pattern.compile("^//\\s?", Pattern.MULTILINE);
        return leadingComment.matcher(text).replaceAll("");
    }

    public static String comment(String text) {
        String[] lines = text.split("\n");
        return Arrays.stream(lines).map(s -> "// " + s).collect(Collectors.joining("\n"));
    }

    public static void registerKPSLanguage() {
        AbstractTokenMakerFactory atmf = (AbstractTokenMakerFactory) TokenMakerFactory.getDefaultInstance();
        atmf.putMapping(KPS_LANGUAGE_ID, ProofScriptHighlighter.class.getName());
        FoldParserManager.get().addFoldParserMapping(KPS_LANGUAGE_ID, new CurlyFoldParser());
    }

    public static void registerCodeTemplates() {
        CodeTemplateManager ctm = RSyntaxTextArea.getCodeTemplateManager();

        URL templateUrl = ScriptUtils.class.getResource("edu.key_project.script.ui.Templates.txt");
        if (templateUrl != null) {
            try {
                String[] lines = IOUtil.readFrom(templateUrl).split("\n");
                for (String line : lines) {
                    if (line.startsWith("#")) {
                        continue;
                    }
                    String[] args = line.split("\\|", 3);
                    try {
                        CodeTemplate ct = new StaticCodeTemplate(args[0],
                                args[1].replaceAll("\\n", "\n"),
                                args[2].replaceAll("\\n", "\n"));
                        ctm.addTemplate(ct);
                    } catch (ArrayIndexOutOfBoundsException e) {
                    }
                }
            } catch (IOException e) {
            }
        }
    }

    public static AutoCompletion createAutoCompletion() {
        CompletionProvider provider = createCompletionProvider();
        return new AutoCompletion(provider);
    }

    /**
     * Create a simple provider that adds some Java-related completions.
     */
    private static CompletionProvider createCompletionProvider() {
        DefaultCompletionProvider provider = new DefaultCompletionProvider();

        String[] words = new String[]{"cases", "case", "try", "closes", "derivable", "default",
                "using", "match", "script", "true", "false", "call", "repeat", "foreach",
                "theonly", "strict", "relax", "while", "if"};
        for (String word : words)
            provider.addCompletion(new BasicCompletion(provider, word));

        KeYApi.getMacroApi().getMacros().forEach(e ->
                provider.addCompletion(new BasicCompletion(provider, e.getScriptCommandName(), "Macro: " + e.getName(),
                        e.getDescription())));

        KeYApi.getScriptCommandApi().getScriptCommands().forEach(e ->
                provider.addCompletion(new BasicCompletion(provider, e.getName(), "Command: " + e.getName(),
                        e.getDocumentation())));
        return provider;
    }
}
