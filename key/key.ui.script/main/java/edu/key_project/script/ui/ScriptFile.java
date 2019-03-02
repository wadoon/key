package edu.key_project.script.ui;

import lombok.Data;
import lombok.NonNull;

import java.io.File;

/**
 * @author Alexander Weigl
 * @version 1 (02.03.19)
 */
@Data
class ScriptFile {
    @NonNull
    private String name;
    private File file;
    private String content;
    private boolean dirty;
}
