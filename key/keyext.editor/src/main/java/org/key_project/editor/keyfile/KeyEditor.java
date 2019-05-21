package org.key_project.editor.keyfile;

import org.fife.ui.rsyntaxtextarea.AbstractTokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument;
import org.fife.ui.rsyntaxtextarea.TokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.folding.CurlyFoldParser;
import org.fife.ui.rsyntaxtextarea.folding.FoldParserManager;
import org.fife.ui.rsyntaxtextarea.parser.AbstractParser;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParseResult;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParserNotice;
import org.fife.ui.rsyntaxtextarea.parser.ParseResult;
import org.key_project.editor.Editor;

/**
 * @author Alexander Weigl
 * @version 1 (21.05.19)
 */
public class KeyEditor extends Editor {
    public static final String KEY_LANGUAGE_ID = "text/key";

    static {
        AbstractTokenMakerFactory atmf = (AbstractTokenMakerFactory) TokenMakerFactory.getDefaultInstance();
        atmf.putMapping(KEY_LANGUAGE_ID, KeYTokenFactory.class.getName());
        FoldParserManager.get().addFoldParserMapping(KEY_LANGUAGE_ID, new CurlyFoldParser());
    }

    public KeyEditor() {
        editor.setAntiAliasingEnabled(true);
        editor.setAutoIndentEnabled(true);
        editor.setCodeFoldingEnabled(false);
        editor.setBracketMatchingEnabled(false);
        editor.setClearWhitespaceLinesEnabled(true);
        editor.setCloseCurlyBraces(true);
        editor.setCloseMarkupTags(false);
        editor.setParserDelay(1000);
        editor.setSyntaxEditingStyle(KEY_LANGUAGE_ID);
        editor.addParser(new KeyEditorParser());
    }
}


class KeyEditorParser extends AbstractParser {
    DefaultParseResult result = new DefaultParseResult(this);

    @Override
    public ParseResult parse(RSyntaxDocument doc, String style) {
        result.clearNotices();
        result.addNotice(new DefaultParserNotice(
                this, "KeYParser is not implemented", 0, 0, 10));
        return null;
    }
}
