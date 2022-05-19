package org.key_project.slicing.ui;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ShowProofStatistics;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Quadruple;
import org.key_project.slicing.AnalysisResults;
import org.key_project.slicing.PreviewDialog;

import javax.swing.*;
import javax.swing.border.EmptyBorder;
import java.awt.*;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.Comparator;

public class RuleStatisticsDialog extends JDialog {
    public RuleStatisticsDialog(Window window, AnalysisResults results) {
        super(window, "Rule Statistics");
        setLayout(new BorderLayout());

        StringBuilder stats = new StringBuilder("<table><thead>");
        for (var a : new String[] { "Rule name", "Total applications", "Useless applications", "Initial useless applications" }) {
            stats.append("<td>").append(a).append("</td>");
        }
        stats.append("</thead><tbody>");

        results.ruleStatistics.entrySet().stream()
                .map(entry -> new Quadruple<>(entry.getValue().first, entry.getValue().second, entry.getValue().third, entry.getKey()))
                .sorted(Comparator.reverseOrder())
                .forEach(a -> {
                    var name = a.fourth;
                    var all = a.first;
                    var useless = a.second;
                    var iua = a.third;
                    stats.append("<tr>");
                    stats.append("<td>").append(name).append("</td>");
                    stats.append("<td>").append(all).append("</td>");
                    stats.append("<td>").append(useless).append("</td>");
                    stats.append("<td>").append(iua).append("</td>");
                    stats.append("</tr>");
                });

        stats.append("</tbody></table>");

        JEditorPane statisticsPane = new JEditorPane("text/html", stats.toString());
        statisticsPane.setEditable(false);
        statisticsPane.setBorder(BorderFactory.createEmptyBorder());
        statisticsPane.setCaretPosition(0);
        statisticsPane.setBackground(MainWindow.getInstance().getBackground());
        statisticsPane.setSize(new Dimension(10, 360));
        statisticsPane.setPreferredSize(
                new Dimension(statisticsPane.getPreferredSize().width + 15, 360));

        JScrollPane scrollPane = new JScrollPane(statisticsPane);
        scrollPane.setBorder(BorderFactory.createEmptyBorder());

        Font myFont = UIManager.getFont(Config.KEY_FONT_PROOF_TREE);
        if (myFont != null) {
            statisticsPane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES,
                    Boolean.TRUE);
            statisticsPane.setFont(myFont);
        }

        JPanel buttonPane = new JPanel();

        JButton okButton = new JButton("Close");
        okButton.addActionListener(event -> {
            dispose();
        });

        buttonPane.add(okButton);

        getRootPane().setDefaultButton(okButton);
        getRootPane().addKeyListener(new KeyAdapter() {

            @Override
            public void keyTyped(KeyEvent e) {
                if (e.getKeyCode() == KeyEvent.VK_ENTER) {
                    getRootPane().getDefaultButton().doClick();
                }
            }
        });

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
