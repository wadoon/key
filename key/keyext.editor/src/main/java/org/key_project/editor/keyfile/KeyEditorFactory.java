package org.key_project.editor.keyfile;

import lombok.val;
import org.key_project.editor.AbstractEditorFactory;
import org.key_project.editor.Editor;

/**
 * @author Alexander Weigl
 * @version 1 (21.05.19)
 */
public class KeyEditorFactory extends AbstractEditorFactory {
    public KeyEditorFactory() {
        super("Key Problem Files", ".kps", KeyEditor.KEY_LANGUAGE_ID);
    }

    @Override
    public Editor open() {
        val e = new KeyEditor();
        e.setMimeType(mimeType);
        return e;
    }
}
