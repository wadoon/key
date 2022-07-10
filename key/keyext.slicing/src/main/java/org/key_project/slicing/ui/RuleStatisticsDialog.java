package org.key_project.slicing.ui;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.util.Quadruple;
import org.key_project.slicing.AnalysisResults;
import org.key_project.slicing.RuleStatistics;

import javax.swing.*;
import java.awt.*;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Dialog that displays the results of the dependency analysis algorithm.
 *
 * @author Arne Keller
 */
public class RuleStatisticsDialog extends JDialog {
    private final transient RuleStatistics statistics;

    public RuleStatisticsDialog(Window window, AnalysisResults results) {
        super(window, "Rule Statistics");

        this.statistics = results.ruleStatistics;

        setLayout(new BorderLayout());

        JEditorPane statisticsPane = new JEditorPane("text/html", "");
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
        KeyStroke stroke = KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0);
        rootPane.registerKeyboardAction(e -> dispose(), stroke, JComponent.WHEN_IN_FOCUSED_WINDOW);

        JButton sortButton1 = new JButton("Sort by name");
        sortButton1.addActionListener(event -> {
            statisticsPane.setText(genTable(
                    statistics.sortBy(Comparator.comparing(it -> it.first))));
            statisticsPane.setCaretPosition(0);
        });
        JButton sortButton2 = new JButton("Sort by total");
        sortButton2.addActionListener(event -> {
            statisticsPane.setText(genTable(
                    statistics.sortBy(
                            Comparator.comparing((Quadruple<String, Integer, Integer, Integer> it) -> it.second).reversed())));
            statisticsPane.setCaretPosition(0);
        });
        JButton sortButton3 = new JButton("Sort by useless");
        sortButton3.addActionListener(event -> {
            statisticsPane.setText(genTable(
                    statistics.sortBy(
                            Comparator.comparing((Quadruple<String, Integer, Integer, Integer> it) -> it.third).reversed())));
            statisticsPane.setCaretPosition(0);
        });
        JButton sortButton4 = new JButton("Sort by initial useless");
        sortButton4.addActionListener(event -> {
            statisticsPane.setText(genTable(
                    statistics.sortBy(
                            Comparator.comparing((Quadruple<String, Integer, Integer, Integer> it) -> it.fourth).reversed())));
            statisticsPane.setCaretPosition(0);
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
                if (e.getKeyCode() == KeyEvent.VK_ENTER || e.getKeyCode() == KeyEvent.VK_ESCAPE) {
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

        statisticsPane.setText(genTable(
                statistics.sortBy(
                        Comparator.comparing((Quadruple<String, Integer, Integer, Integer> it) -> it.second).reversed())));
        statisticsPane.setCaretPosition(0);

        setVisible(true);
    }

    private String genTable(List<Quadruple<String, Integer, Integer, Integer>> rules) {
        StringBuilder stats = new StringBuilder("<table><thead>");
        for (var a : new String[] { "Rule name", "Total applications", "Useless applications", "Initial useless applications" }) {
            stats.append("<td>").append(a).append("</td>");
        }
        stats.append("</thead><tbody>");

        // summary row
        var uniqueRules = rules.size();
        var totalSteps = rules.stream().mapToInt(it -> it.second).sum();
        var uselessSteps = rules.stream().mapToInt(it -> it.third).sum();
        var initialUseless = rules.stream().mapToInt(it -> it.fourth).sum();
        stats.append("<tr>");
        stats.append("<td>").append(String.format("(all %d rules)", uniqueRules)).append("</td>");
        stats.append("<td>").append(totalSteps).append("</td>");
        stats.append("<td>").append(uselessSteps).append("</td>");
        stats.append("<td>").append(initialUseless).append("</td>");
        stats.append("</tr>");
        // next summary row
        var rulesBranching = rules.stream().filter(it -> statistics.branches(it.first)).collect(Collectors.toList());
        var uniqueRules2 = rulesBranching.size();
        var totalSteps2 = rulesBranching.stream().mapToInt(it -> it.second).sum();
        var uselessSteps2 = rulesBranching.stream().mapToInt(it -> it.third).sum();
        var initialUseless2 = rulesBranching.stream().mapToInt(it -> it.fourth).sum();
        stats.append("<tr>");
        stats.append("<td>").append(String.format("(%d branching rules)", uniqueRules2)).append("</td>");
        stats.append("<td>").append(totalSteps2).append("</td>");
        stats.append("<td>").append(uselessSteps2).append("</td>");
        stats.append("<td>").append(initialUseless2).append("</td>");
        stats.append("</tr>");
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
