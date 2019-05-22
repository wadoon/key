package org.key_project.editor.java;

import org.fife.ui.rsyntaxtextarea.AbstractTokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.TokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.folding.CurlyFoldParser;
import org.fife.ui.rsyntaxtextarea.folding.FoldParserManager;
import org.key_project.editor.Editor;
import org.key_project.editor.keyfile.KeYTokenFactory;

/**
 * @author Alexander Weigl
 * @version 1 (22.05.19)
 */
public class JavaJMLEditor extends Editor {
    public static final String MIME_TYPE = "text/java";

    static {
        AbstractTokenMakerFactory atmf = (AbstractTokenMakerFactory) TokenMakerFactory.getDefaultInstance();
        atmf.putMapping(MIME_TYPE, JavaJMLTokenFactory.class.getName());
        FoldParserManager.get().addFoldParserMapping(MIME_TYPE, new CurlyFoldParser());
    }

}
