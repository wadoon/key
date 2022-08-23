package org.key_project.slicing.ui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.slicing.AnalysisResults;
import org.key_project.slicing.DependencyTracker;
import org.key_project.slicing.SlicingExtension;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import javax.swing.*;
import javax.swing.border.TitledBorder;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

public class SlicingLeftPanel extends JPanel implements TabPanel, KeYSelectionListener {
    /**
     * The icon of this panel.
     */
    public static final Icon INFO_ICON = IconFactory.SLICE_ICON.get(MainWindow.TAB_ICON_SIZE);
    /**
     * ID of this panel.
     */
    public static final String NAME = "slicingPane";

    /**
     * Logger of this class.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(SlicingLeftPanel.class);
    /**
     * If set to true, the panel will include information on the current usage of the Java Heap
     * and a button that calls {@link System#gc()}.
     */
    private static final boolean ENABLE_DEBUGGING_UI = false;

    private final transient KeYMediator mediator;
    private final transient SlicingExtension extension;
    private final JButton sliceProof;
    private final JButton runAnalysis;
    private final JButton showRuleStatistics;
    private transient Proof currentProof = null;
    private final JLabel memoryStats;
    private final JLabel graphNodes;
    private final JLabel graphEdges;
    private final JLabel totalSteps;
    private final JLabel usefulSteps;
    private final JLabel totalBranches;
    private final JLabel usefulBranches;
    private final JCheckBox abbreviateFormulas;
    private final JCheckBox doDependencyAnalysis;
    private final JCheckBox doDeduplicateRuleApps;
    private final JPanel timings;

    private int graphNodesNr = 0;
    private int graphEdgesNr = 0;
    private boolean updateGraphLabels = false;
    private Timer updateGraphLabelsTimer;
    private Timer updateHeapMemoryTimer;

    public SlicingLeftPanel(KeYMediator mediator, SlicingExtension extension) {
        super();

        setName(NAME);

        var mainPanel = new JPanel();
        mainPanel.setLayout(new BoxLayout(mainPanel, BoxLayout.Y_AXIS));

        var panel1 = new JPanel();
        panel1.setLayout(new BoxLayout(panel1, BoxLayout.Y_AXIS));
        panel1.setBorder(new TitledBorder("Dependency graph"));

        var panel2 = new JPanel();
        panel2.setLayout(new BoxLayout(panel2, BoxLayout.Y_AXIS));
        panel2.setBorder(new TitledBorder("Dependency analysis"));

        abbreviateFormulas = new JCheckBox("Abbreviate formulas");
        var button = new JButton("Export as DOT");
        button.addActionListener(this::exportDot);
        var button2 = new JButton("Show rendering of graph");
        button2.addActionListener(this::previewGraph);
        runAnalysis = new JButton("Run analysis");
        runAnalysis.addActionListener(this::analyzeProof);
        sliceProof = new JButton("Slice proof");
        sliceProof.addActionListener(this::sliceProof);
        var button6 = new JButton("call System.gc()");
        button6.addActionListener(e -> {
            System.gc();
            Runtime.getRuntime().gc();
        });
        showRuleStatistics = new JButton("Show rule statistics");
        showRuleStatistics.addActionListener(this::showRuleStatistics);
        graphNodes = new JLabel();
        graphEdges = new JLabel();
        resetGraphLabels();
        totalSteps = new JLabel();
        usefulSteps = new JLabel();
        totalBranches = new JLabel();
        usefulBranches = new JLabel();
        doDependencyAnalysis = new JCheckBox("Dependency analysis");
        doDependencyAnalysis.setSelected(true);
        doDependencyAnalysis.addActionListener(e -> resetLabels());
        doDeduplicateRuleApps = new JCheckBox("De-duplicate rule applications");
        doDeduplicateRuleApps.setSelected(false);
        doDeduplicateRuleApps.addActionListener(e -> resetLabels());

        abbreviateFormulas.setAlignmentX(Component.LEFT_ALIGNMENT);
        button.setAlignmentX(Component.LEFT_ALIGNMENT);
        button2.setAlignmentX(Component.LEFT_ALIGNMENT);
        panel1.add(graphNodes);
        panel1.add(graphEdges);
        panel1.add(abbreviateFormulas);
        panel1.add(button);
        panel1.add(button2);

        panel2.add(totalSteps);
        panel2.add(usefulSteps);
        panel2.add(totalBranches);
        panel2.add(usefulBranches);
        panel2.add(doDependencyAnalysis);
        panel2.add(doDeduplicateRuleApps);
        panel2.add(runAnalysis);
        panel2.add(showRuleStatistics);

        timings = new JPanel();
        timings.setLayout(new BoxLayout(timings, BoxLayout.Y_AXIS));
        timings.setBorder(new TitledBorder("Execution timings"));
        timings.setVisible(false);

        memoryStats = new JLabel("Java Heap Usage: ?");

        panel1.setAlignmentX(Component.LEFT_ALIGNMENT);
        panel2.setAlignmentX(Component.LEFT_ALIGNMENT);
        sliceProof.setAlignmentX(Component.LEFT_ALIGNMENT);
        button6.setAlignmentX(Component.LEFT_ALIGNMENT);
        memoryStats.setAlignmentX(Component.LEFT_ALIGNMENT);
        timings.setAlignmentX(Component.LEFT_ALIGNMENT);
        mainPanel.add(panel1);
        mainPanel.add(panel2);
        mainPanel.add(sliceProof);
        if (ENABLE_DEBUGGING_UI) {
            mainPanel.add(button6);
            mainPanel.add(memoryStats);
        }
        mainPanel.add(timings);

        setLayout(new BorderLayout());
        mainPanel.setAlignmentX(Component.LEFT_ALIGNMENT);
        add(new JScrollPane(mainPanel));

        invalidate();

        this.mediator = mediator;
        this.extension = extension;

        updateGraphLabelsTimer = new Timer(100, e -> {
            if (updateGraphLabels) {
                displayGraphLabels();
                updateGraphLabelsTimer.stop();
            }
        });
        updateHeapMemoryTimer = new Timer(100, e -> {
            var runtime = Runtime.getRuntime();
            var total = runtime.totalMemory();
            var used = total - runtime.freeMemory();
            memoryStats.setText(String.format(
                    "Java Heap Usage: %d MB / %d MB", used / 1024 / 1024, total / 1024 / 1024));
        });
        updateHeapMemoryTimer.start();
    }

    private void exportDot(ActionEvent e) {
        if (currentProof == null) {
            return;
        }
        KeYFileChooser fileChooser = KeYFileChooser.getFileChooser(
                "Choose filename to save dot file");
        fileChooser.setFileFilter(KeYFileChooser.DOT_FILTER);
        fileChooser.setSelectedFile(new File("export.dot"));
        int result = fileChooser.showSaveDialog((JComponent) e.getSource());
        if (result == JFileChooser.APPROVE_OPTION) {
            File file = fileChooser.getSelectedFile();
            try (BufferedWriter writer = new BufferedWriter(
                    new OutputStreamWriter(new FileOutputStream(file)))) {
                String text = extension
                        .trackers.get(currentProof)
                        .exportDot(abbreviateFormulas.isSelected());
                writer.write(text);
            } catch (IOException any) {
                any.printStackTrace();
                IssueDialog.showExceptionDialog(MainWindow.getInstance(), any);
            }
        }
    }

    private void showRuleStatistics(ActionEvent e) {
        if (currentProof == null) {
            return;
        }
        var results = this.analyzeProof(e);
        if (results != null) {
            new RuleStatisticsDialog(
                    SwingUtilities.getWindowAncestor((JComponent) e.getSource()),
                    results
            );
        }
    }

    private void previewGraph(ActionEvent e) {
        if (currentProof == null) {
            return;
        }
        String text = extension
                .trackers.get(currentProof)
                .exportDot(abbreviateFormulas.isSelected());
        new PreviewDialog(SwingUtilities.getWindowAncestor((JComponent) e.getSource()), text);
    }

    private AnalysisResults analyzeProof(ActionEvent e) {
        if (currentProof == null) {
            return null;
        }
        var results = extension.trackers.get(currentProof).analyze(
                doDependencyAnalysis.isSelected(), doDeduplicateRuleApps.isSelected());
        if (results != null) {
            displayResults(results);
        }
        return results;
    }

    private void sliceProof(ActionEvent event) {
        if (currentProof == null) {
            return;
        }
        analyzeProof(event);
        try {
            var path = extension.trackers.get(currentProof).sliceProof();
            SwingUtilities.invokeLater(() -> mediator.getUI().loadProblem(path.toFile()));
        } catch (Exception e) {
            LOGGER.error("failed to slice proof", e);
            SwingUtilities.invokeLater(() ->
                    IssueDialog.showExceptionDialog(MainWindow.getInstance(), e)
            );
        }
    }

    private void resetLabels() {
        totalSteps.setText("Total steps: ?");
        usefulSteps.setText("Useful steps: ?");
        totalBranches.setText("Total branches: ?");
        usefulBranches.setText("Useful branches: ?");
        showRuleStatistics.setEnabled(false);
        var algoSelectionSane = doDependencyAnalysis.isSelected()
                || doDeduplicateRuleApps.isSelected();
        runAnalysis.setEnabled(algoSelectionSane);
        sliceProof.setEnabled(algoSelectionSane);
        timings.setVisible(false);
        timings.removeAll();
    }

    private void displayResults(AnalysisResults results) {
        totalSteps.setText("Total steps: " + results.totalSteps);
        usefulSteps.setText("Useful steps: " + results.usefulStepsNr);
        totalBranches.setText("Total branches: " + results.proof.countBranches());
        usefulBranches.setText("Useful branches: "
                + (results.proof.countBranches() - results.uselessBranches.size()));
        showRuleStatistics.setEnabled(true);
        timings.removeAll();
        var coll = results.executionTime.executionTimes()
                .map(action -> (Collection<String>)
                        List.of(action.first, "" + action.second + " ms"))
                .collect(Collectors.toList());
        var html = HtmlFactory.generateTable(
                List.of("Algorithm", "Time"),
                new boolean[] { false, false },
                Optional.of(new String[] { null, "right" }),
                coll,
                null
        );
        timings.add(HtmlFactory.createComponent(html));
        timings.setVisible(true);
    }

    private void resetGraphLabels() {
        graphNodes.setText("Graph nodes: ?");
        graphEdges.setText("Graph edges: ?");
    }

    private void displayGraphLabels() {
        graphNodes.setText("Graph nodes: " + graphNodesNr);
        graphEdges.setText("Graph edges: " + graphEdgesNr);
    }

    @Nonnull
    @Override
    public String getTitle() {
        return "Proof Slicing";
    }

    @Override
    public Icon getIcon() {
        return INFO_ICON;
    }

    @Nonnull
    @Override
    public JComponent getComponent() {
        return this;
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        currentProof = e.getSource().getSelectedProof();
        resetLabels();
        resetGraphLabels();
        var tracker = extension.trackers.get(currentProof);
        if (tracker == null) {
            return;
        }
        if (tracker.getAnalysisResults() != null) {
            displayResults(tracker.getAnalysisResults());
        }
        if (tracker.getDependencyGraph() != null) {
            graphNodesNr = tracker.getDependencyGraph().countNodes();
            graphEdgesNr = tracker.getDependencyGraph().countEdges();
            displayGraphLabels();
        }
    }

    public void ruleAppliedOnProof(Proof proof, DependencyTracker tracker) {
        currentProof = proof;
        graphNodesNr = tracker.getDependencyGraph().countNodes();
        graphEdgesNr = tracker.getDependencyGraph().countEdges();
        updateGraphLabels = true;
        updateGraphLabelsTimer.start();
    }

    public void proofDisposed(Proof proof) {
        if (proof == currentProof) {
            currentProof = null;
        }
    }
}
