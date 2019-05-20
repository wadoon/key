package org.key_project.editor;

import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import lombok.Getter;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.RSyntaxUtilities;
import org.fife.ui.rtextarea.Gutter;
import org.fife.ui.rtextarea.RTextScrollPane;
import org.key_project.util.RandomName;

import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import java.awt.*;
import java.nio.file.Path;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.19)
 */
public class Editor extends JPanel {
    public static final String PROP_DIRTY = "DIRTY";
    public static final String PROP_PATH = "PATH";

    @Getter
    private final RSyntaxTextArea editor;

    @Getter
    private final Gutter gutter;

    @Getter
    private final RTextScrollPane editorView;

    private final String name = RandomName.getRandomName("-") + ".kps";
    private final DefaultMultipleCDockable dockable = new DefaultMultipleCDockable(
            EditorFacade.getEditorDockableFactory(), this);

    protected JToolBar toolBarActions = new JToolBar();

    @Getter
    private boolean dirty;

    @Getter
    private Path path;

    public Editor() {
        super(new BorderLayout(5, 5));
        toolBarActions.setFloatable(false);
        editor = new RSyntaxTextArea();
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
        add(editorView);

        addPropertyChangeListener(it -> dockable.setTitleText(getTitle()));
        dockable.setTitleText(getTitle());
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
        firePropertyChange(PROP_DIRTY, oldDirty, dirty);
    }

    public void setPath(Path f) {
        Path oldFile = path;
        path = f;
        firePropertyChange(PROP_PATH, oldFile, f);
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
}
