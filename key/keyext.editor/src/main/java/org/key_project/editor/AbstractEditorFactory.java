package org.key_project.editor;

import lombok.Getter;
import lombok.RequiredArgsConstructor;
import lombok.val;
import org.jetbrains.annotations.NotNull;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.Collections;

/**
 * An editor factory with good defaults.
 *
 * @author Alexander Weigl
 * @version 1 (21.05.19)
 */
@RequiredArgsConstructor
public abstract class AbstractEditorFactory implements EditorFactory {
    @Getter
    private final String name;
    @Getter
    private final String suffix;
    @Getter
    private final String mimeType;

    @Override
    public @NotNull Collection<String> getFileSuffixes() {
        return Collections.singleton(suffix);
    }

    @Override
    public Editor open(Path path) throws IOException {
        if (path.toString().endsWith(suffix)) {
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
