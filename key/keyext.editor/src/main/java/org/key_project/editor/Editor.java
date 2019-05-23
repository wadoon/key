package org.key_project.editor;

import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.symbolic_execution.util.SideProofStore;
import lombok.Getter;
import org.fife.rsta.ui.CollapsibleSectionPanel;
import org.fife.rsta.ui.GoToDialog;
import org.fife.rsta.ui.search.FindToolBar;
import org.fife.rsta.ui.search.ReplaceToolBar;
import org.fife.rsta.ui.search.SearchEvent;
import org.fife.rsta.ui.search.SearchListener;
import org.fife.ui.rsyntaxtextarea.ErrorStrip;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.RSyntaxUtilities;
import org.fife.ui.rtextarea.*;
import org.key_project.util.RandomName;

import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.BadLocationException;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.beans.PropertyChangeSupport;
import java.nio.file.Path;

import static javax.swing.JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.19)
 */
public class Editor extends DefaultMultipleCDockable implements SearchListener {
    public static final String PROP_DIRTY = "DIRTY";
    public static final String PROP_PATH = "PATH";

    @Getter
    protected final RSyntaxTextArea editor;

    @Getter
    protected final Gutter gutter;

    @Getter
    private final RTextScrollPane editorView;

    private final String name = RandomName.getRandomName("-") + ".kps";
    private final DefaultMultipleCDockable dockable = this;

    private final PropertyChangeSupport eventSupport = new PropertyChangeSupport(this);
    private final JPanel pane;

    protected JToolBar toolBarActions = new JToolBar();

    @Getter
    private boolean dirty;

    @Getter
    private Path path;

    public Editor() {
        super(EditorFacade.getEditorDockableFactory());
        pane = (JPanel) getContentPane();
        pane.setLayout(new BorderLayout(5, 5));

        FindToolBar findToolBar = new FindToolBar(this);
        ReplaceToolBar replaceToolBar = new ReplaceToolBar(this);
        replaceToolBar.setSearchContext(findToolBar.getSearchContext());


        toolBarActions.setFloatable(false);

        editor = new RSyntaxTextArea();
        //EditorFacade.getEditorTheme().apply(editor);
        editorView = new RTextScrollPane(editor);
        gutter = RSyntaxUtilities.getGutter(editor);
        editor.setAntiAliasingEnabled(true);
        editor.setCloseCurlyBraces(true);
        editor.setCloseMarkupTags(true);
        editor.setCodeFoldingEnabled(true);
        dockable.setCloseable(true);
        dockable.setRemoveOnClose(true);
        editor.getDocument().addDocumentListener(new DocumentListener() {
            @Override
            public void insertUpdate(DocumentEvent e) {
                update();
            }

            private void update() {
                setDirty(true);
            }

            @Override
            public void removeUpdate(DocumentEvent e) {
                update();
            }

            @Override
            public void changedUpdate(DocumentEvent e) {
                update();
            }
        });
        add(toolBarActions, BorderLayout.NORTH);
        CollapsibleSectionPanel csp = new CollapsibleSectionPanel();
        csp.add(editorView);
        add(csp);

        ErrorStrip errorStrip = new ErrorStrip(editor);
        add(errorStrip, BorderLayout.LINE_END);


        eventSupport.addPropertyChangeListener(it -> dockable.setTitleText(getTitle()));
        dockable.setTitleText(getTitle());

        pane.registerKeyboardAction(
                EditorExtension.getSaveAction(),
                EditorExtension.getSaveAction().getAcceleratorKey(),
                WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);

        pane.registerKeyboardAction(
                EditorExtension.getActionLoad(),
                EditorExtension.getActionLoad().getAcceleratorKey(),
                WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);

        pane.registerKeyboardAction(
                EditorExtension.getActionSaveAs(),
                EditorExtension.getActionSaveAs().getAcceleratorKey(),
                WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);

        KeyAction actionGoto = new GoToLineAction();
        pane.registerKeyboardAction(
                actionGoto,
                actionGoto.getAcceleratorKey(),
                WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);


        KeyStroke ks = KeyStroke.getKeyStroke(KeyEvent.VK_F, InputEvent.CTRL_DOWN_MASK);
        Action a = csp.addBottomComponent(ks, findToolBar);
        a.putValue(Action.NAME, "Show Find Search Bar");
        pane.registerKeyboardAction(a, ks, WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        ks = KeyStroke.getKeyStroke(KeyEvent.VK_R, InputEvent.CTRL_DOWN_MASK);
        a = csp.addBottomComponent(ks, replaceToolBar);
        a.putValue(Action.NAME, "Show Replace Search Bar");
        pane.registerKeyboardAction(a, ks, WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
    }

    public String getTitle() {
        return (path != null ? path.getFileName() : name) + (dirty ? "*" : "");
    }

    public String getText() {
        return editor.getText();
    }

    public void setText(String textContent) {
        editor.setText(textContent);
    }

    public void setDirty(boolean dirty) {
        boolean oldDirty = isDirty();
        this.dirty = dirty;
        eventSupport.firePropertyChange(PROP_DIRTY, oldDirty, dirty);
    }

    public Path getPath() {
        return path;
    }

    public void setPath(Path f) {
        Path oldFile = path;
        path = f;
        eventSupport.firePropertyChange(PROP_PATH, oldFile, f);
    }

    public DefaultMultipleCDockable getDockable() {
        return dockable;
    }

    public String getMimeType() {
        return editor.getSyntaxEditingStyle();
    }

    public void setMimeType(String mime) {
        editor.setSyntaxEditingStyle(mime);
    }

    @Override
    public void searchEvent(SearchEvent e) {

        SearchEvent.Type type = e.getType();
        SearchContext context = e.getSearchContext();
        SearchResult result = null;

        switch (type) {
            default: // Prevent FindBugs warning later
            case MARK_ALL:
                result = SearchEngine.markAll(editor, context);
                break;
            case FIND:
                result = SearchEngine.find(editor, context);
                if (!result.wasFound()) {
                    UIManager.getLookAndFeel().provideErrorFeedback(editor);
                }
                break;
            case REPLACE:
                result = SearchEngine.replace(editor, context);
                if (!result.wasFound()) {
                    UIManager.getLookAndFeel().provideErrorFeedback(editor);
                }
                break;
            case REPLACE_ALL:
                result = SearchEngine.replaceAll(editor, context);
                JOptionPane.showMessageDialog(null, result.getCount() +
                        " occurrences replaced.");
                break;
        }

        String text = null;
        if (result.wasFound()) {
            text = "Text found; occurrences marked: " + result.getMarkedCount();
        } else if (type == SearchEvent.Type.MARK_ALL) {
            if (result.getMarkedCount() > 0) {
                text = "Occurrences marked: " + result.getMarkedCount();
            } else {
                text = "";
            }
        } else {
            text = "Text not found";
        }
    }

    @Override
    public String getSelectedText() {
        return null;
    }

    private class GoToLineAction extends KeyAction {
        GoToLineAction() {
            setName("Go To Line...");
            int c = InputEvent.CTRL_DOWN_MASK;
            putValue(ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_L, c));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            GoToDialog dialog = new GoToDialog((Frame) null);
            dialog.setMaxLineNumberAllowed(editor.getLineCount());
            dialog.setVisible(true);
            int line = dialog.getLineNumber();
            if (line > 0) {
                try {
                    editor.setCaretPosition(editor.getLineStartOffset(line - 1));
                } catch (BadLocationException ble) { // Never happens
                    UIManager.getLookAndFeel().provideErrorFeedback(editor);
                    ble.printStackTrace();
                }
            }
        }

    }
}
