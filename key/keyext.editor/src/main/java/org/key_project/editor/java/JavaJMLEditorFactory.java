package org.key_project.editor.java;

import lombok.val;
import org.key_project.editor.AbstractEditorFactory;
import org.key_project.editor.Editor;

/**
 * @author Alexander Weigl
 * @version 1 (22.05.19)
 */
public class JavaJMLEditorFactory extends AbstractEditorFactory {
    public JavaJMLEditorFactory() {
        super("Java+JML file", ".java", JavaJMLEditor.MIME_TYPE);
    }

    @Override
    public Editor open() {
        val editor = new JavaJMLEditor();
        editor.setMimeType(JavaJMLEditor.MIME_TYPE);
        return editor;
    }
}
