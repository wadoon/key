package org.key_project.editor.java;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.CompilationUnit;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument;
import org.fife.ui.rsyntaxtextarea.parser.AbstractParser;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParseResult;
import org.fife.ui.rsyntaxtextarea.parser.ParseResult;

import javax.swing.text.BadLocationException;

/**
 * @author Alexander Weigl
 * @version 1 (02.08.19)
 */
public class JavaJMLKeYLinter extends AbstractParser {
    private DefaultParseResult result = new DefaultParseResult(this);

    @Override
    public ParseResult parse(RSyntaxDocument doc, String style) {
        result.clearNotices();
        try {
            String text = doc.getText(0, doc.getLength());
            Services services = MainWindow.getInstance().getMediator().getServices();
            CompilationUnit comp = new Recoder2KeY(services, services.getNamespaces())
                    .readCompilationUnit(text);
            System.out.println("XXX");
        } catch (BadLocationException e) {
            e.printStackTrace();
        } catch (Exception e) {
            e.printStackTrace();
        }
        return result;
    }
}
