package org.key_project.editor;

import bibliothek.gui.dock.common.CControl;
import bibliothek.gui.dock.common.event.CFocusListener;
import bibliothek.gui.dock.common.intern.CDockable;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import lombok.Getter;
import org.jetbrains.annotations.NotNull;

import javax.swing.*;
import javax.swing.filechooser.FileFilter;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;

/**
 * The extension which brings a text editors to KeY.
 * <p>
 * This extension also has an extension: You add language support
 * by implementing {@link EditorFactory}.
 * <p>
 * Extension brings several global editor actions: new, load, save, and saveAs.
 *
 * @author Alexander Weigl
 * @version 1 (21.05.19)
 */
public class EditorExtension implements KeYGuiExtension,
        KeYGuiExtension.Startup, KeYGuiExtension.Toolbar,
        KeYGuiExtension.MainMenu {
    public static final float ICON_SIZE = 16;
    private static final String EDITOR_MENU = "File.Editor";

    private static SaveAction actionSave;
    private static SaveAsAction actionSaveAs;
    private static LoadAction actionLoad;

    @Getter
    private static OpenCurrentAsFileAction actionOpenCurrentProofFile;

    @Getter
    private NewAction actionNew;

    private JFileChooser fileChooser;

    @Getter
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
            return (Editor) (mainWindow.getDockControl().getFocusedCDockable());
        } catch (ClassCastException e) {
        }
        return null;
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        if (mainWindow == null) {
            CControl control = window.getDockControl();
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

    public JFileChooser getFileChooser() {
        if (fileChooser == null) {
            fileChooser = new JFileChooser();
        }

        for (FileFilter f : fileChooser.getChoosableFileFilters()) {
            fileChooser.removeChoosableFileFilter(f);
        }
        EditorFacade.getFileFilters().forEach(fileChooser::addChoosableFileFilter);

        return fileChooser;
    }

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        init(mainWindow, null);
        JToolBar tb = new JToolBar();
        tb.add(actionNew);
        tb.add(actionLoad);
        tb.add(actionSave);
        tb.add(actionSaveAs);
        //tb.addSeparator();
        //tb.add(actionOpenCurrentProofFile);
        return tb;
    }

    @Override
    public @NotNull List<Action> getMainMenuActions(@NotNull MainWindow mainWindow) {
        init(mainWindow, null);
        return Arrays.asList(
                actionNew,
                actionLoad,
                actionSave,
                actionSaveAs,
                actionOpenCurrentProofFile);
    }

    private class OpenCurrentAsFileAction extends KeyAction {
        public OpenCurrentAsFileAction() {
            setName("Open Current Proof As File");
            setMenuPath(EDITOR_MENU);
            lookupAcceleratorKey();
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
                        Editor editor = EditorFacade.open(f.toPath());
                        if (editor != null)
                            EditorFacade.addEditor(editor, mainWindow);
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
            setName("Save current editor as…");
            setTooltip("Save the current focused editor under a new path.");
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.SAVE, MainWindow.TOOLBAR_ICON_SIZE));
            setMenuPath(EDITOR_MENU);
            lookupAcceleratorKey();
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            Editor editor = getCurrentEditor();
            JFileChooser fc = getFileChooser();
            if (editor != null) {
                Path file = editor.getPath();
                if (file != null) {
                    fc.setCurrentDirectory(file.getParent().toFile());
                    fc.setSelectedFile(file.toFile());
                }
                int c = fc.showSaveDialog(mainWindow);
                if (c == JFileChooser.APPROVE_OPTION) {
                    File f = fc.getSelectedFile();
                    try {
                        Files.writeString(f.toPath(), editor.getText());
                        editor.setPath(f.toPath());
                        editor.setDirty(false);
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
            setName("Save current editor");
            setTooltip("Save current editor");
            setMenuPath(EDITOR_MENU);
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.DOWNLOAD, ICON_SIZE));
            lookupAcceleratorKey();
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            Editor editor = getCurrentEditor();
            if (editor != null) {
                if (editor.getPath() != null) {
                    try {
                        Files.writeString(editor.getPath(), editor.getText());
                        editor.setDirty(false);
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
            setName("Open script file ...");
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.UPLOAD, ICON_SIZE));
            setMenuPath(EDITOR_MENU);
            lookupAcceleratorKey();
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            int c = getFileChooser().showOpenDialog(mainWindow);
            if (c == JFileChooser.APPROVE_OPTION) {
                File file = fileChooser.getSelectedFile();
                Editor editor = EditorFacade.open(file.toPath());
                addEditor(editor);
            }
        }
    }

    private class NewAction extends KeyAction {
        public NewAction() {
            setName("New script file");
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.FILE_MEDICAL, ICON_SIZE));
            setTooltip("New script file");
            setMenuPath(EDITOR_MENU);
            lookupAcceleratorKey();
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
            int x = c.getWidth();
            int y = c.getHeight();
            menu.show(c, x, y);
        }
    }
}
