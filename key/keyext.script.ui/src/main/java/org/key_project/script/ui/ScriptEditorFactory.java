package org.key_project.script.ui;

import lombok.val;
import org.key_project.editor.Editor;
import org.key_project.editor.EditorFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

/**
 * @author Alexander Weigl
 * @version 1 (21.05.19)
 */
public class ScriptEditorFactory implements EditorFactory {
    @Override
    public String getName() {
        return "KeY Proof Script";
    }

    @Override
    public Editor open(Path path) throws IOException {
        if (path.getFileName().endsWith(".kps")) {
            val e = open();
            e.setText(Files.readString(path));
            e.setPath(path);
            e.setDirty(false);
            return e;
        }
        return null;
    }

    @Override
    public Editor open(String mimeType) {
        if (mimeType.equals(ScriptUtils.KPS_LANGUAGE_ID))
            return open();
        return null;
    }

    @Override
    public Editor open() {
        val e = new ScriptEditor();
        e.setMimeType(ScriptUtils.KPS_LANGUAGE_ID);
        return e;
    }
}
