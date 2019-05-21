package org.key_project.editor;

import java.io.IOException;
import java.nio.file.Path;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.19)
 */
public interface EditorFactory {
    String getName();

    Editor open(Path path) throws IOException;

    Editor open(String mimeType);

    Editor open();

}
