package org.key_project.editor.java;

import org.fife.ui.rsyntaxtextarea.RSyntaxDocument;
import org.fife.ui.rsyntaxtextarea.parser.AbstractParser;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParseResult;
import org.fife.ui.rsyntaxtextarea.parser.ParseResult;

public class JavaJMLLinter extends AbstractParser {
    private DefaultParseResult result = new DefaultParseResult(this);

    @Override
    public ParseResult parse(RSyntaxDocument doc, String style) {
        result.clearNotices();

        return result;
    }
}
