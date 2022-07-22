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

    private final transient KeYMediator mediator;
    private final transient SlicingExtension extension;
    private transient Proof currentProof = null;
    private final JLabel totalSteps;
    private final JLabel usefulSteps;
    private final JCheckBox abbreviateFormulas;
    private final JCheckBox doDependencyAnalysis;
    private final JCheckBox doDeduplicateRuleApps;

    public SlicingLeftPanel(KeYMediator mediator, SlicingExtension extension) {
        super();

        setName(NAME);

        setLayout(new GridBagLayout());

        var panel = new JPanel();
        panel.setLayout(new BoxLayout(panel, BoxLayout.Y_AXIS));
        panel.setBorder(new TitledBorder("Dependency analysis"));

        abbreviateFormulas = new JCheckBox("Abbreviate formulas");
        var button = new JButton("Export .dot");
        button.addActionListener(this::exportDot);
        var button2 = new JButton("View formula graph");
        button2.addActionListener(this::previewGraph);
        var button3 = new JButton("Run analysis");
        button3.addActionListener(this::analyzeProof);
        var button4 = new JButton("Slice proof");
        button4.addActionListener(this::sliceProof);
        var button5 = new JButton("Show rule statistics");
        button5.addActionListener(this::showRuleStatistics);
        totalSteps = new JLabel();
        usefulSteps = new JLabel();
        doDependencyAnalysis = new JCheckBox("Dependency analysis");
        doDependencyAnalysis.setSelected(true);
        doDependencyAnalysis.addActionListener(e -> resetLabels());
        doDeduplicateRuleApps = new JCheckBox("De-duplicate rule applications");
        doDeduplicateRuleApps.setSelected(false);
        doDeduplicateRuleApps.addActionListener(e -> resetLabels());

        resetLabels();
        panel.add(totalSteps);
        panel.add(usefulSteps);
        panel.add(doDependencyAnalysis);
        panel.add(doDeduplicateRuleApps);
        panel.add(button3);
        panel.add(button5);
        var y = 0;
        GridBagConstraints c = new GridBagConstraints();
        c.gridx = 0;
        c.gridy = y++;
        c.fill = GridBagConstraints.HORIZONTAL;
        c.weightx = 1.0;
        c.weighty = 0.0;
        c.anchor = GridBagConstraints.PAGE_START;
        add(panel, c);
        c = new GridBagConstraints();
        c.gridx = 0;
        c.gridy = y++;
        c.weighty = 0.0;
        c.anchor = GridBagConstraints.FIRST_LINE_START;
        add(abbreviateFormulas, c);
        c = new GridBagConstraints();
        c.gridx = 0;
        c.gridy = y++;
        c.weighty = 0.0;
        c.anchor = GridBagConstraints.FIRST_LINE_START;
        add(button, c);
        c = new GridBagConstraints();
        c.gridx = 0;
        c.gridy = y++;
        c.weighty = 0.0;
        c.anchor = GridBagConstraints.FIRST_LINE_START;
        add(button2, c);
        c = new GridBagConstraints();
        c.gridx = 0;
        c.gridy = y++;
        c.weighty = 1.0;
        c.anchor = GridBagConstraints.FIRST_LINE_START;
        add(button4, c);
        invalidate();

        this.mediator = mediator;
        this.extension = extension;
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
    }

    private void displayResults(AnalysisResults results) {
        totalSteps.setText("Total steps: " + results.totalSteps);
        usefulSteps.setText("Useful steps: " + results.usefulStepsNr);
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
        this.currentProof = e.getSource().getSelectedProof();
        resetLabels();
        var tracker = extension.trackers.get(currentProof);
        if (tracker == null) {
            return;
        }
        if (tracker.getAnalysisResults() != null) {
            displayResults(tracker.getAnalysisResults());
        }
    }
}
