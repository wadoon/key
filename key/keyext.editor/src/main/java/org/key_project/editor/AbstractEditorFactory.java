package org.key_project.editor;

import lombok.val;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

/**
 * @author Alexander Weigl
 * @version 1 (21.05.19)
 */
public abstract class AbstractEditorFactory implements EditorFactory {
    public final String name, suffix, mimeType;

    public AbstractEditorFactory(String name, String suffix, String mimeType) {
        this.name = name;
        this.suffix = suffix;
        this.mimeType = mimeType;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public Editor open(Path path) throws IOException {
        if (path.endsWith(suffix)) {
            val e = open();
            e.setText(Files.readString(path));
            e.setDirty(false);
            e.setPath(path);
            e.setMimeType(mimeType);
            return e;
        }
        return null;
    }

    @Override
    public Editor open(String mimeType) {
        if (mimeType.equals(this.mimeType)) {
            Editor e = open();
            e.setMimeType(mimeType);
            return e;
        }
        return null;
    }
}
