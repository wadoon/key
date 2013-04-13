package se.gu.svanefalk.tackey.editor.formatting;

import org.eclipse.jface.text.formatter.IFormattingStrategy;

public class DeclarationFormattingStrategy implements IFormattingStrategy {

    @Override
    public void formatterStarts(String initialIndentation) {
System.out.println("Start DECLARATION");
    }

    @Override
    public String format(String content, boolean isLineStart,
            String indentation, int[] positions) {
        System.out.println("CONTENT: " + content);
        return content;
    }

    @Override
    public void formatterStops() {
        // TODO Auto-generated method stub
    }
}