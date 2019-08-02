package org.key_project.editor.java;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import lombok.Getter;
import org.fife.ui.rsyntaxtextarea.*;
import org.fife.ui.rsyntaxtextarea.folding.CurlyFoldParser;
import org.fife.ui.rsyntaxtextarea.folding.FoldParserManager;
import org.fife.ui.rsyntaxtextarea.templates.CodeTemplate;
import org.fife.ui.rsyntaxtextarea.templates.StaticCodeTemplate;
import org.key_project.editor.Editor;
import org.key_project.editor.EditorExtension;
import org.key_project.util.RandomName;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.io.BufferedInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Properties;

/**
 * @author Alexander Weigl
 * @version 1 (22.05.19)
 */
public class JavaJMLEditor extends Editor {
    public static final String MIME_TYPE = "text/java";
    private static final ColorSettings.ColorProperty JML_BACKGROUND_COLOR =
            ColorSettings.define("[editor]jmlBackground", "A descent color for the background of JML annotations.",
                    new Color(140, 220, 255));

    static {
        AbstractTokenMakerFactory atmf = (AbstractTokenMakerFactory) TokenMakerFactory.getDefaultInstance();
        atmf.putMapping(MIME_TYPE, JavaJMLTokenFactory.class.getName());
        FoldParserManager.get().addFoldParserMapping(MIME_TYPE, new CurlyFoldParser());
        RSyntaxTextArea.setTemplatesEnabled(true);

        URL snippetUrl = JavaJMLEditor.class.getResource("snippets.xml");
        if (snippetUrl != null) {
            try (InputStream s = new BufferedInputStream(snippetUrl.openStream())) {
                CodeTemplateManager ctm = RSyntaxTextArea.getCodeTemplateManager();
                Properties p = new Properties();
                p.loadFromXML(s);
                p.forEach((key, value) -> {
                    String v = value.toString();
                    String[] t = v.split("[#]");
                    if (t.length > 1) {
                        CodeTemplate ct = new StaticCodeTemplate(key.toString(), t[0], t[1]);
                        ctm.addTemplate(ct);
                    } else {
                        CodeTemplate ct = new StaticCodeTemplate(key.toString(), v, null);
                        ctm.addTemplate(ct);
                    }
                });
                System.out.println("Java snippets loaded");
            } catch (IOException e) {
                e.printStackTrace();
            }
        } else {
            System.err.println("Could not find snippets.xml");
        }
    }

    @Getter
    private KeyAction actionOpen = new OpenAction();

    public JavaJMLEditor() {
        super(RandomName.getRandomName("") + ".java");
        setMimeType(MIME_TYPE);
        editor.setAntiAliasingEnabled(true);
        editor.setCloseCurlyBraces(true);
        editor.setCloseMarkupTags(false);
        editor.setCodeFoldingEnabled(true);
        editor.addParser(new JavaJMLLinter());
        editor.addParser(new JavaJMLKeYLinter());

        editor.setAnimateBracketMatching(true);
        editor.setMarkOccurrences(true);
        editor.setMarkOccurrencesDelay(1000);
        editor.setSecondaryLanguageBackground(1, JML_BACKGROUND_COLOR.get());
        toolBarActions.add(actionOpen);

        editor.setSyntaxScheme(new SyntaxScheme(true) {
            @Override
            public Style getStyle(int index) {
                try {
                    return super.getStyle(index);
                } catch (ArrayIndexOutOfBoundsException e) {
                    return super.getStyle(0);
                }
            }
        });

    }

    private class OpenAction extends KeyAction {
        public OpenAction() {
            setName("Open...");
            setIcon(IconFactory.PROOF_MANAGEMENT.get(16f));
            setAcceleratorKey(KeyStroke.getKeyStroke(KeyEvent.VK_ENTER, InputEvent.CTRL_DOWN_MASK));
            lookupAcceleratorKey();
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            //Save file:
            EditorExtension.getSaveAction().actionPerformed(e);
            if (getPath() != null) {
                MainWindow.getInstance().getMediator().getUI().loadProblem(
                        getPath().toFile());
            }
        }
    }
}
