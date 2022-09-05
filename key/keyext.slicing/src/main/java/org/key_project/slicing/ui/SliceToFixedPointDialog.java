package org.key_project.slicing.ui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.slicing.AnalysisResults;

import javax.swing.*;
import java.awt.*;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;

public class SliceToFixedPointDialog extends JDialog implements KeYSelectionListener {
    private final KeYMediator mediator;
    private final JButton closeButton;
    private JEditorPane logPane = null;
    private boolean cancelled = false;
    private boolean done = false;

    private Function<Void, AnalysisResults> analyzeButton;
    private Runnable sliceButton;
    private SliceToFixedPointWorker worker;

    private Collection<Collection<String>> tableRows = new ArrayList<>();
    private Map<String, Integer> slicedAway = new HashMap<>();

    public SliceToFixedPointDialog(KeYMediator mediator, Window window,
                                   Function<Void, AnalysisResults> analyzeCallback,
                                   Runnable sliceButton) {
        super(window, "Slice to fixed point");

        this.mediator = mediator;
        this.analyzeButton = x -> {
            System.out.println("intermediate callback requests analysis");
            AnalysisResults results = null;
            try {
                results = analyzeCallback.apply(null);
            } catch (Throwable t) {
                t.printStackTrace();
            }
            System.out.println("intermediate callback has results");
            if (results != null) {
                try {
                    // record useless rule applications in map
                    var queue = new ArrayDeque<>(List.of(results.proof.root()));
                    while (!queue.isEmpty()) {
                        var node = queue.pop();
                        node.childrenIterator().forEachRemaining(queue::add);
                        if (node.getAppliedRuleApp() == null || results.usefulSteps.contains(node)) {
                            continue;
                        }
                        var name = node.getAppliedRuleApp().rule().displayName();
                        if (node.childrenCount() > 1) {
                            name = name + "*";
                        }
                        slicedAway.compute(
                                name,
                                (k, v) -> v == null ? 1 : v + 1
                        );
                    }
                    var filename = results.proof.getProofFile();
                    var label = filename != null ?
                            filename.getName() : results.proof.name().toString();
                    tableRows.add(List.of(
                            label,
                            "" + results.totalSteps,
                            "" + results.usefulStepsNr,
                            "" + results.proof.countBranches(),
                            "" + results.usefulBranchesNr));
                    SwingUtilities.invokeLater(this::updateTable);
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }
            System.out.println("forwarding");
            if (cancelled) {
                done();
                return null;
            } else {
                return results;
            }
        };
        this.sliceButton = sliceButton;

        logPane = new JEditorPane("text/html", "");
        logPane.setEditable(false);
        logPane.setBorder(BorderFactory.createEmptyBorder());
        logPane.setCaretPosition(0);
        logPane.setBackground(MainWindow.getInstance().getBackground());
        logPane.setSize(new Dimension(10, 360));
        logPane.setPreferredSize(
                new Dimension(logPane.getPreferredSize().width + 15, 360));

        JScrollPane scrollPane = new JScrollPane(logPane);
        scrollPane.setBorder(BorderFactory.createEmptyBorder());

        Font myFont = UIManager.getFont(Config.KEY_FONT_PROOF_TREE);
        if (myFont != null) {
            logPane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES,
                    Boolean.TRUE);
            logPane.setFont(myFont);
        }

        JPanel buttonPane = new JPanel();

        closeButton = new JButton("Close");
        closeButton.setEnabled(false);
        closeButton.addActionListener(event -> dispose());
        JButton cancel = new JButton("Cancel");
        cancel.addActionListener(event -> {
            cancel.setEnabled(false);
            mediator.removeKeYSelectionListener(this);
            cancelled = true;
        });

        buttonPane.add(cancel);
        buttonPane.add(closeButton);

        getRootPane().setDefaultButton(closeButton);

        setLayout(new BorderLayout());
        add(scrollPane, BorderLayout.CENTER);
        add(buttonPane, BorderLayout.PAGE_END);

        this.updateTable();
        setMinimumSize(new Dimension(800, 600));
        setLocationRelativeTo(window);

        setVisible(true);
    }

    private void updateTable() {
        var html = HtmlFactory.generateTable(
                List.of("Filename", "Total steps", "Useful steps", "Total branches", "Useful branches"),
                new boolean[]{false, false, false, false, false},
                Optional.of(new String[]{null, "right", "right", "right", "right"}),
                tableRows,
                null
        );
        var data = slicedAway
                .entrySet().stream()
                // sort inferences rule sliced away most to the start
                .sorted(Comparator.comparing(x -> -x.getValue()))
                .map(x -> (Collection<String>) List.of(x.getKey(), x.getValue().toString()))
                .collect(Collectors.toList());
        var html2 = HtmlFactory.generateTable(
                List.of("Inference rule", "Times sliced away"),
                new boolean[]{false, false},
                Optional.of(new String[]{null, "right"}),
                data,
                null
        );
        logPane.setText(html + "<hr/>" + html2);
    }

    public void start(Proof proof) {
        worker = new SliceToFixedPointWorker(proof, null, closeButton, analyzeButton, sliceButton, this::done);
        worker.execute();
    }

    private void done() {
        done = true;
        SwingUtilities.invokeLater(() ->
                closeButton.setEnabled(true)
        );
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        if (done) {
            SwingUtilities.invokeLater(() ->
                    mediator.removeKeYSelectionListener(this)
            );
            return;
        }
        System.out.println("selection changed");
        if (e.getSource().getSelectedProof() != null
                && e.getSource().getSelectedProof().closed()) {
            if (e.getSource().getSelectedProof() == worker.proof) {
                return;
            }
            if (cancelled) {
                done();
                return;
            }
            worker = new SliceToFixedPointWorker(e.getSource().getSelectedProof(), worker.proof, closeButton, analyzeButton, sliceButton, this::done);
            worker.execute();
        }
    }
}
