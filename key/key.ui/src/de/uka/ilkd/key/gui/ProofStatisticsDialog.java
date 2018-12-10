package de.uka.ilkd.key.gui;

import java.awt.Dialog;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Window;
import java.io.IOException;

import javax.swing.BorderFactory;
import javax.swing.JDialog;
import javax.swing.JEditorPane;
import javax.swing.JTextPane;
import javax.swing.UIManager;
import javax.swing.text.BadLocationException;
import javax.swing.text.MutableAttributeSet;
import javax.swing.text.html.HTMLDocument;
import javax.swing.text.html.HTMLEditorKit;

import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.util.Debug;


public class ProofStatisticsDialog extends JDialog {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private static final String TITLE = "Proof Statistics";

    private ProofStatisticsDialog(Window parentComponent, String title) {
        super(parentComponent, title != null ? title : TITLE, Dialog.ModalityType.DOCUMENT_MODAL);
        setDefaultCloseOperation(DISPOSE_ON_CLOSE);
        pack();
        setLocationRelativeTo(null);
    }

    private ProofStatisticsDialog(Window parentComponent) {
        this(parentComponent, null);
    }

    /**
     * Shows the dialog.
     */
    public static void show(Window parentComponent, String message, Statistics.HTMLMessage htmlStatisticsMessage) {
        ProofStatisticsDialog dialog = new ProofStatisticsDialog(parentComponent, message);
        JTextPane textPane = new JTextPane();
        textPane.setContentType("text/html");
        textPane.setEditable(false);
        textPane.setBorder(BorderFactory.createEmptyBorder());
        textPane.setCaretPosition(0);
        textPane.setBackground(MainWindow.getInstance().getBackground());
        textPane.setVisible(true);
        textPane.setEnabled(true);

        final HTMLEditorKit htmlKit = (HTMLEditorKit)textPane.getEditorKitForContentType("text/html");
        final HTMLDocument htmlDoc = (HTMLDocument) textPane.getStyledDocument();
        final MutableAttributeSet mats = textPane.getInputAttributes();

        try {
            htmlKit.insertHTML(htmlDoc, htmlDoc.getLength(), htmlStatisticsMessage.getMessageString(), 0, 0, null);
        } catch (BadLocationException | IOException e) {
            e.printStackTrace();
        } finally {
            htmlDoc.setCharacterAttributes(0, htmlDoc.getLength(), mats, false);
        }
        // textPane.setPreferredSize(new Dimension(20, htmlDoc.getLength()));

        Font myFont = UIManager.getFont(Config.KEY_FONT_PROOF_TREE);
        if (myFont != null) {
            textPane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES, Boolean.TRUE);
            textPane.setFont(myFont);
        } else {
            Debug.out("KEY_FONT_PROOF_TREE not available. Use standard font.");
        }

        dialog.setContentPane(textPane);
        dialog.setMinimumSize(new Dimension(htmlStatisticsMessage.getWidth(), htmlStatisticsMessage.getHeight()));
        // dialog.setPreferredSize(new Dimension(20, htmlDoc.getLength()));
        dialog.setMaximumSize(new Dimension(parentComponent.getWidth(), parentComponent.getHeight()));
        dialog.setVisible(true);
        dialog.setEnabled(true);
        dialog.dispose();
        // JOptionPane.showMessageDialog(parentComponent, scrollPane,
        //        "Proof Statistics", JOptionPane.INFORMATION_MESSAGE);
        // FIXME
    }

}
