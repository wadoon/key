package org.key_project.script.ui;

import lombok.val;
import org.jetbrains.annotations.NotNull;
import org.key_project.editor.AbstractEditorFactory;
import org.key_project.editor.Editor;
import org.key_project.editor.EditorFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

/**
 * @author Alexander Weigl
 * @version 1 (21.05.19)
 */
public class ScriptEditorFactory extends AbstractEditorFactory {
    public ScriptEditorFactory() {
        super("KeY Proof Script", ".kps", ScriptUtils.KPS_LANGUAGE_ID);
    }

    @NotNull
    @Override
    public Editor open() {
        val e = new ScriptEditor();
        e.setMimeType(ScriptUtils.KPS_LANGUAGE_ID);
        return e;
    }
}
