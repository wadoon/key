package rsta;

import lexerFactories.LanguageSupport;
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;
import java.awt.*;

public class TextEditor extends JDialog {

    private JTabbedPane tabs;

    public TextEditor(Dialog parent) {
        super(parent);
        tabs = new JTabbedPane();
        tabs.setPreferredSize(new Dimension(400, 400));
        setContentPane(tabs);
        setTitle("Text Editor");
        setDefaultCloseOperation(DISPOSE_ON_CLOSE);
        pack();
        setLocationRelativeTo(null);
    }

    public void addPanel(String input, LanguageSupport lang) {
        RSyntaxTextArea textArea = new RSyntaxTextArea();
        RSyntaxDocument doc = (RSyntaxDocument) textArea.getDocument();
        // Set the token maker used to create RSTA tokens out of the input stream.
        doc.setSyntaxStyle(lang.tokenMaker);
        // Set the syntax scheme which defines how to display different types of tokens.
        textArea.setSyntaxScheme(lang.syntaxScheme);
        textArea.setText(input);

        RTextScrollPane sp = new RTextScrollPane(textArea);
        tabs.add(sp);
        pack();
    }

}
