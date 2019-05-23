package org.key_project.editor;

import bibliothek.gui.dock.common.CControl;
import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import bibliothek.gui.dock.common.event.CFocusListener;
import bibliothek.gui.dock.common.intern.CDockable;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.EditMostRecentFileAction;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.proof.Proof;
import lombok.Getter;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

/**
 * @author Alexander Weigl
 * @version 1 (21.05.19)
 */
public class EditorExtension implements KeYGuiExtension, KeYGuiExtension.Startup, KeYGuiExtension.Toolbar {
    public static final float ICON_SIZE = 16;
    private static SaveAction actionSave;
    private static SaveAsAction actionSaveAs;
    private static LoadAction actionLoad;
    private static OpenCurrentAsFileAction actionOpenCurrentProofFile;

    @Getter
    private NewAction actionNew;
    @Getter
    private JFileChooser fileChooser = new JFileChooser();
    private CControl control;
    private MainWindow mainWindow;

    public static LoadAction getActionLoad() {
        return actionLoad;
    }

    public static SaveAsAction getActionSaveAs() {
        return actionSaveAs;
    }

    public static KeyAction getSaveAction() {
        return actionSave;
    }

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
            actionNew = new NewAction();
            actionLoad = new LoadAction(window);
            actionSaveAs = new SaveAsAction(window);
            actionSave = new SaveAction(window);
            actionOpenCurrentProofFile = new OpenCurrentAsFileAction();

            control.addFocusListener(new CFocusListener() {
                @Override
                public void focusGained(CDockable cDockable) {
                    boolean e = getCurrentEditor() != null;
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
        tb.add(actionNew);
        tb.add(actionLoad);
        tb.add(actionSave);
        tb.add(actionSaveAs);
        tb.addSeparator();
        tb.add(actionOpenCurrentProofFile);
        return tb;
    }

    private class OpenCurrentAsFileAction extends KeyAction {
        public OpenCurrentAsFileAction() {
            setName("Open Current Proof As File...");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            if (mainWindow.getRecentFiles() != null
                    && mainWindow.getRecentFiles().getMostRecent() != null) {
                final String recentFile = mainWindow.getRecentFiles()
                        .getMostRecent().getAbsolutePath();
                if (recentFile != null) {
                    File f = new File(recentFile);
                    try {
                        EditorFacade.open(f.toPath());
                    } catch (Exception exc) {
                        setEnabled(false);
                    }
                }
            }
        }
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
            Editor editor = getCurrentEditor();
            if (editor != null) {
                Path file = editor.getPath();
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
            Editor editor = getCurrentEditor();
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
                Editor editor = EditorFacade.open(file.toPath());
                addEditor(editor);
            }
        }
    }

    private class NewAction extends KeyAction {
        public NewAction() {
            setName("New file");
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.FILE, ICON_SIZE));
            setTooltip("Store script file");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JPopupMenu menu = new JPopupMenu();
            EditorFacade.getEditorFactories().forEach(it -> {
                JMenuItem item = new JMenuItem(it.getName());
                item.addActionListener(evt ->
                        EditorFacade.addEditor(it.open(), mainWindow));
                menu.add(item);
            });
            Component c = (Component) e.getSource();
            int x = c.getLocationOnScreen().x + c.getWidth();
            int y = c.getLocationOnScreen().y + c.getHeight();
            menu.show(mainWindow, x, y);
        }
    }
}
