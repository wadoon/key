package org.key_project.slicing.ui;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.util.Quadruple;
import org.key_project.slicing.AnalysisResults;

import javax.swing.*;
import java.awt.*;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;

public class RuleStatisticsDialog extends JDialog {
    private final transient List<Quadruple<String, Integer, Integer, Integer>> rules;

    public RuleStatisticsDialog(Window window, AnalysisResults results) {
        super(window, "Rule Statistics");
        setLayout(new BorderLayout());

        rules = results.ruleStatistics.entrySet().stream()
                .map(entry -> new Quadruple<>(entry.getKey(), entry.getValue().first, entry.getValue().second, entry.getValue().third))
                .collect(Collectors.toList());
        rules.sort(Comparator.comparing((Quadruple<String, Integer, Integer, Integer> it) -> it.second).reversed());

        JEditorPane statisticsPane = new JEditorPane("text/html", genTable());
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
        okButton.addActionListener(event -> dispose());

        JButton sortButton1 = new JButton("Sort by name");
        sortButton1.addActionListener(event -> {
            rules.sort(Comparator.comparing(it -> it.first));
            statisticsPane.setText(genTable());
        });
        JButton sortButton2 = new JButton("Sort by total");
        sortButton2.addActionListener(event -> {
            rules.sort(Comparator.comparing((Quadruple<String, Integer, Integer, Integer> it) -> it.second).reversed());
            statisticsPane.setText(genTable());
        });
        JButton sortButton3 = new JButton("Sort by useless");
        sortButton3.addActionListener(event -> {
            rules.sort(Comparator.comparing((Quadruple<String, Integer, Integer, Integer> it) -> it.third).reversed());
            statisticsPane.setText(genTable());
        });
        JButton sortButton4 = new JButton("Sort by initial useless");
        sortButton4.addActionListener(event -> {
            rules.sort(Comparator.comparing((Quadruple<String, Integer, Integer, Integer> it) -> it.fourth).reversed());
            statisticsPane.setText(genTable());
        });

        buttonPane.add(sortButton1);
        buttonPane.add(sortButton2);
        buttonPane.add(sortButton3);
        buttonPane.add(sortButton4);
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

    private String genTable() {
        StringBuilder stats = new StringBuilder("<table><thead>");
        for (var a : new String[] { "Rule name", "Total applications", "Useless applications", "Initial useless applications" }) {
            stats.append("<td>").append(a).append("</td>");
        }
        stats.append("</thead><tbody>");

        rules.forEach(a -> {
            var name = a.first;
            var all = a.second;
            var useless = a.third;
            var iua = a.fourth;
            stats.append("<tr>");
            stats.append("<td>").append(name).append("</td>");
            stats.append("<td>").append(all).append("</td>");
            stats.append("<td>").append(useless).append("</td>");
            stats.append("<td>").append(iua).append("</td>");
            stats.append("</tr>");
        });

        stats.append("</tbody></table>");

        return stats.toString();
    }
}
