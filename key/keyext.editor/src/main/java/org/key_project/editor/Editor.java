package org.key_project.editor;

import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import de.uka.ilkd.key.gui.actions.KeyAction;
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

import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.beans.PropertyChangeSupport;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;

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
    private final Color EXECUTION_HIGHLIGHT = Color.LIGHT_GRAY;
    @Getter
    private final RTextScrollPane editorView;

    private final String name;

    private final DefaultMultipleCDockable dockable = this;

    private final PropertyChangeSupport eventSupport = new PropertyChangeSupport(this);
    private final JPanel contentPanel;
    protected final CollapsibleSectionPanel rootPanel;

    protected JToolBar toolBarActions = new JToolBar();

    @Getter
    private boolean dirty;


    private Path path;

    private Map<Integer, Object> highlightedLines = new HashMap<>();

    public Editor(String name) {
        super(EditorFacade.getEditorDockableFactory());
        this.name = name;
        contentPanel = (JPanel) getContentPane();
        contentPanel.setLayout(new BorderLayout(5, 5));

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
        this.rootPanel = new CollapsibleSectionPanel();
        rootPanel.add(editorView);
        add(rootPanel);

        ErrorStrip errorStrip = new ErrorStrip(editor);
        add(errorStrip, BorderLayout.LINE_END);


        eventSupport.addPropertyChangeListener(it -> dockable.setTitleText(getTitle()));
        dockable.setTitleText(getTitle());

        EditorExtension.getSaveAction().registerIn(contentPanel,
                WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        EditorExtension.getActionLoad().registerIn(contentPanel,
                WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        EditorExtension.getActionSaveAs().registerIn(contentPanel,
                WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);

        KeyAction actionGoto = new GoToLineAction();
        actionGoto.registerIn(contentPanel, WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);

        contentPanel.registerKeyboardAction(
                this::increaseFontSize,
                KeyStroke.getKeyStroke(KeyEvent.VK_PLUS, InputEvent.CTRL_DOWN_MASK),
                WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);

        contentPanel.registerKeyboardAction(
                this::decreaseFontSize,
                KeyStroke.getKeyStroke(KeyEvent.VK_MINUS, InputEvent.CTRL_DOWN_MASK),
                WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);

        KeyStroke ks = KeyStroke.getKeyStroke(KeyEvent.VK_F, InputEvent.CTRL_DOWN_MASK);
        Action a = rootPanel.addBottomComponent(ks, findToolBar);
        a.putValue(Action.NAME, "Show Find Search Bar");
        contentPanel.registerKeyboardAction(a, ks, WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        ks = KeyStroke.getKeyStroke(KeyEvent.VK_R, InputEvent.CTRL_DOWN_MASK);
        a = rootPanel.addBottomComponent(ks, replaceToolBar);
        a.putValue(Action.NAME, "Show Replace Search Bar");
        contentPanel.registerKeyboardAction(a, ks, WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);


        Font font = Font.getFont("Fira Code");
        if(font != null) {
            font.deriveFont(12f);
            editor.setFont(font);
        }
    }

    private void decreaseFontSize(ActionEvent actionEvent) {
        Font f = getEditor().getFont();
        getEditor().setFont(f.deriveFont(f.getSize() - 2f));
        System.out.println("Editor.decreaseFontSize");
    }

    private void increaseFontSize(ActionEvent actionEvent) {
        Font f = getEditor().getFont();
        getEditor().setFont(f.deriveFont(f.getSize() + 2f));
        System.out.println("Editor.increaseFontSize");
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

    /**
     * Highlight whole line
     *
     * @param line
     * @throws BadLocationException
     */
    public void highlightExecutionLine(int line) throws BadLocationException {
        Object tag = editor.addLineHighlight(line, EXECUTION_HIGHLIGHT);
        highlightedLines.put(line, tag);
    }

    /**
     * Remove all highlighted lines
     *
     * @throws BadLocationException
     */
    public void unHighlightAllExecutionLines() throws BadLocationException {
        for (Map.Entry<Integer, Object> entry : highlightedLines.entrySet()) {
            editor.removeLineHighlight(entry.getValue());
        }
        highlightedLines.clear();

    }

    public void unHighlightExecutionLines(int line) throws BadLocationException {
        if (highlightedLines.containsKey(line)) {
            Object tag = highlightedLines.get(line);
            editor.removeLineHighlight(tag);
            highlightedLines.remove(line, tag);
        }

    }

    public void highlightRange(int charStart, int charStop, Color c) throws BadLocationException {
        editor.getHighlighter().addHighlight(charStart, charStop, new DefaultHighlighter.DefaultHighlightPainter(c));
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