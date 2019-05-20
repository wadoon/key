package org.key_project.editor;

import bibliothek.gui.dock.common.CControl;
import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import bibliothek.gui.dock.common.event.CFocusListener;
import bibliothek.gui.dock.common.intern.CDockable;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import lombok.Getter;
import lombok.val;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

/**
 * @author Alexander Weigl
 * @version 1 (21.05.19)
 */
public class EditorExtension implements KeYGuiExtension, KeYGuiExtension.Startup, KeYGuiExtension.Toolbar {
    public static final float ICON_SIZE = 16;
    @Getter
    private SaveAction actionSave;
    @Getter
    private SaveAsAction actionSaveAs;
    @Getter
    private LoadAction actionLoad;
    @Getter
    private JFileChooser fileChooser = new JFileChooser();

    private CControl control;

    private MainWindow mainWindow;

    public void addEditor(Editor editor) {
        EditorFacade.addEditor(editor, mainWindow);
    }

    public Editor getCurrentEditor() {
        try {
            return (Editor)
                    ((DefaultMultipleCDockable)
                            mainWindow.getDockControl().getFocusedCDockable()).getContentPane();
        } catch (ClassCastException e) {
        }
        return null;
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        if (mainWindow == null) {
            this.control = window.getDockControl();
            this.mainWindow = window;
            control.addMultipleDockableFactory("editors", EditorFacade.getEditorDockableFactory());
            actionLoad = new LoadAction(window);
            actionSaveAs = new SaveAsAction(window);
            actionSave = new SaveAction(window);

            control.addFocusListener(new CFocusListener() {
                @Override
                public void focusGained(CDockable cDockable) {
                    val e = getCurrentEditor() != null;
                    actionSave.setEnabled(e);
                    actionSaveAs.setEnabled(e);
                }

                @Override
                public void focusLost(CDockable cDockable) {

                }
            });
        }
    }

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        init(mainWindow, null);
        JToolBar tb = new JToolBar();
        tb.add(actionLoad);
        tb.add(actionSave);
        tb.add(actionSaveAs);
        return tb;
    }

    class SaveAsAction extends MainWindowAction {
        public SaveAsAction(MainWindow mw) {
            super(mw);
            setName("Save as…");
            setTooltip("Save the current proof scripts");
            setMenuPath("File");
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.SAVE, MainWindow.TOOLBAR_ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            val editor = getCurrentEditor();
            if (editor != null) {
                val file = editor.getPath();
                if (file != null) {
                    fileChooser.setCurrentDirectory(file.getParent().toFile());
                    fileChooser.setSelectedFile(file.toFile());
                }
                int c = fileChooser.showSaveDialog(mainWindow);
                if (c == JFileChooser.APPROVE_OPTION) {
                    File f = fileChooser.getSelectedFile();
                    try {
                        Files.writeString(f.toPath(), editor.getText());
                    } catch (IOException e1) {
                        e1.printStackTrace();
                    }
                }
            } else {
                mainWindow.setStatusLine("No editor found");
            }
        }
    }

    class SaveAction extends MainWindowAction {
        public SaveAction(MainWindow mw) {
            super(mw);
            setName("Save");
            setTooltip("Store script file");
            setMenuPath("File");
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.DOWNLOAD, ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            val editor = getCurrentEditor();
            if (editor != null) {
                if (editor.getPath() != null) {
                    try {
                        Files.writeString(editor.getPath(), editor.getText());
                    } catch (IOException e1) {
                        e1.printStackTrace();
                    }
                } else {
                    getActionSaveAs().actionPerformed(e);
                }
            } else {
                mainWindow.setStatusLine("No editor found.");
            }
        }
    }

    class LoadAction extends MainWindowAction {
        public LoadAction(MainWindow mw) {
            super(mw);
            setName("Load proof script");
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.UPLOAD, ICON_SIZE));
            setMenuPath("File");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            int c = fileChooser.showOpenDialog(mainWindow);
            if (c == JFileChooser.APPROVE_OPTION) {
                File file = fileChooser.getSelectedFile();
                val editor = EditorFacade.open(file.toPath());
                addEditor(editor);
            }
        }
    }
}
