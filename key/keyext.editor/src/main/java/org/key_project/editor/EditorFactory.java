package org.key_project.editor;

import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Collection;

/**
 * A factory which constructs instances of {@link Editor}.
 *
 * @author Alexander Weigl
 * @version 1 (20.05.19)
 */
public interface EditorFactory {
    /**
     * A description of this editor factory, e.g. the file types
     */
    @NotNull String getName();

    /**
     * Return an possible empty list of file suffixes.
     * <p>
     * Needed for the file chooser dialog.
     */
    @NotNull Collection<String> getFileSuffixes();

    /**
     * Returns an editor with the contents of {@code path }
     * if this factory is suitable for the given path.
     *
     * @param path a path to a resources
     * @throws IOException if the path is not readable
     */
    @Nullable Editor open(@NotNull Path path) throws IOException;

    /**
     * Returns an editor if this factory is suitable for the given mimeType.
     *
     * @param mimeType string value
     * @return null if this factory does not correspond to the mime type
     */
    @Nullable Editor open(String mimeType);

    /**
     * @return Always a fresh editor!
     */
    @NotNull Editor open();
}
