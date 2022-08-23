package org.key_project.slicing.ui;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.util.Pair;

import javax.swing.*;
import javax.swing.event.HyperlinkEvent;
import javax.swing.event.HyperlinkListener;
import java.awt.*;
import java.awt.event.KeyEvent;
import java.util.function.Consumer;

public class HtmlDialog extends JDialog {

    public HtmlDialog(Window window, String title, String html, Consumer<Pair<Integer, Integer>> linkPressedCallback) {
        super(window, title);

        setLayout(new BorderLayout());

        JEditorPane htmlContent = new JEditorPane("text/html", html);
        htmlContent.setEditable(false);
        htmlContent.setBorder(BorderFactory.createEmptyBorder());
        htmlContent.setCaretPosition(0);
        htmlContent.setBackground(MainWindow.getInstance().getBackground());
        htmlContent.setSize(new Dimension(10, 360));
        htmlContent.setPreferredSize(
                new Dimension(Math.min(800, htmlContent.getPreferredSize().width + 15), 360));
        if (linkPressedCallback != null) {
            htmlContent.addHyperlinkListener(event -> {
                if (event.getEventType() == HyperlinkEvent.EventType.ACTIVATED) {
                    var descriptor = event.getDescription().substring(1);
                    var parts = descriptor.split("_");
                    var column = Integer.parseInt(parts[0]);
                    var idx = Integer.parseInt(parts[1]);
                    linkPressedCallback.accept(new Pair<>(column, idx));
                }
            });
        }

        JScrollPane scrollPane = new JScrollPane(htmlContent);
        scrollPane.setBorder(BorderFactory.createEmptyBorder());

        JPanel buttonPane = new JPanel();

        JButton okButton = new JButton("Close");
        okButton.addActionListener(event -> dispose());
        KeyStroke stroke = KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0);
        rootPane.registerKeyboardAction(e -> dispose(), stroke, JComponent.WHEN_IN_FOCUSED_WINDOW);

        buttonPane.add(okButton);

        getRootPane().setDefaultButton(okButton);

        setLayout(new BorderLayout());
        add(scrollPane, BorderLayout.CENTER);
        add(buttonPane, BorderLayout.PAGE_END);

        int w = 50
                + Math.max(
                scrollPane.getPreferredSize().width,
                buttonPane.getPreferredSize().width
        );
        int h = scrollPane.getPreferredSize().height
                + buttonPane.getPreferredSize().height
                + 100;
        setSize(w, h);
        setLocationRelativeTo(window);

        setVisible(true);
    }
}
