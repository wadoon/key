package se.gu.svanefalk.tackey.editor.formatting;

import org.eclipse.jface.text.formatter.IFormattingStrategy;

public class DefaultFormattingStrategy implements IFormattingStrategy {

    @Override
    public void formatterStarts(String initialIndentation) {
        System.out.println("START DEFAULT");
    }

    @Override
    public String format(String content, boolean isLineStart,
            String indentation, int[] positions) {
        return "";
    }

    @Override
    public void formatterStops() {

    }

}
