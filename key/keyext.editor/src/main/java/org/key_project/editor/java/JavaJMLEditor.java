package org.key_project.editor.java;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import lombok.Getter;
import org.fife.ui.rsyntaxtextarea.AbstractTokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.TokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.folding.CurlyFoldParser;
import org.fife.ui.rsyntaxtextarea.folding.FoldParserManager;
import org.key_project.editor.Editor;
import org.key_project.editor.EditorExtension;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;

/**
 * @author Alexander Weigl
 * @version 1 (22.05.19)
 */
public class JavaJMLEditor extends Editor {
    public static final String MIME_TYPE = "text/java";
    private static final ColorSettings.ColorProperty JML_BACKGROUND_COLOR =
            ColorSettings.define("[editor]jmlBackground", "A descent color for the background of JML annotations.",
                    new Color(100, 180, 255));

    @Getter
    private KeyAction actionOpen = new OpenAction();

    static {
        AbstractTokenMakerFactory atmf = (AbstractTokenMakerFactory) TokenMakerFactory.getDefaultInstance();
        atmf.putMapping(MIME_TYPE, JavaJMLTokenFactory.class.getName());
        FoldParserManager.get().addFoldParserMapping(MIME_TYPE, new CurlyFoldParser());
    }

    public JavaJMLEditor() {
        setMimeType(MIME_TYPE);
        editor.setAntiAliasingEnabled(true);
        editor.setCloseCurlyBraces(true);
        editor.setCloseMarkupTags(false);
        editor.setCodeFoldingEnabled(true);
        editor.addParser(new JavaJMLLinter());

        editor.setAnimateBracketMatching(true);
        editor.setMarkOccurrences(true);
        editor.setMarkOccurrencesDelay(1000);
        editor.setSecondaryLanguageBackground(1, JML_BACKGROUND_COLOR.get());

        toolBarActions.add(actionOpen);
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
            MainWindow.getInstance().getMediator().getUI().loadProblem(
                    getPath().toFile());
        }
    }
}
