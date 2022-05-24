package org.key_project.slicing.ui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindowTabbedPane;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.slicing.AnalysisResults;
import org.key_project.slicing.SlicingExtension;

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

public class SlicingLeftPanel extends JPanel implements TabPanel {

    public static final Icon INFO_ICON = IconFactory.SLICE_ICON.get(MainWindowTabbedPane.TAB_ICON_SIZE);
    public static final String NAME = "slicingPane";

    private final transient KeYMediator mediator;
    private final transient SlicingExtension extension;
    private final JLabel totalSteps;
    private final JLabel usefulSteps;
    private final JCheckBox abbreviateFormulas;

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
        resetLabels();
        panel.add(totalSteps);
        panel.add(usefulSteps);
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
        var currentProof = extension.currentProof;
        if (currentProof == null || currentProof.countNodes() < 2) {
            return;
        }
        KeYFileChooser fileChooser = KeYFileChooser.getFileChooser(
                "Choose filename to save dot file");
        fileChooser.setFileFilter(KeYFileChooser.DOT_FILTER);
        fileChooser.setSelectedFile(new File("export.dot"));
        int result = fileChooser.showSaveDialog((JComponent) e.getSource());
        if (result == JFileChooser.APPROVE_OPTION) {
            File file = fileChooser.getSelectedFile();
            try(BufferedWriter writer = new BufferedWriter(
                    new OutputStreamWriter(new FileOutputStream(file)));) {
                String text = extension.trackers.get(currentProof).exportDot(abbreviateFormulas.isSelected());
                writer.write(text);
            } catch (IOException any) {
                any.printStackTrace();
                assert false;
            }
        }
    }

    public void proofSelected() {
        resetLabels();
        var tracker = extension.trackers.get(extension.currentProof);
        if (tracker == null) {
            return;
        }
        if (tracker.analyze() != null) {
            displayResults(tracker.analyze());
        }
    }

    private void showRuleStatistics(ActionEvent e) {
        if (extension.currentProof == null) {
            return;
        }
        this.analyzeProof(e);
        var results = extension.trackers.get(extension.currentProof).analyze();
        if (results != null) {
            new RuleStatisticsDialog(SwingUtilities.getWindowAncestor((JComponent) e.getSource()), results);
        }
    }

    private void previewGraph(ActionEvent e) {
        if (extension.currentProof == null || extension.currentProof.countNodes() < 2) {
            return;
        }
        String text = extension.trackers.get(extension.currentProof).exportDot(abbreviateFormulas.isSelected());
        new PreviewDialog(SwingUtilities.getWindowAncestor((JComponent) e.getSource()), text);
    }

    private void analyzeProof(ActionEvent e) {
        if (extension.currentProof == null) {
            return;
        }
        var results = extension.trackers.get(extension.currentProof).analyze();
        if (results != null) {
            displayResults(results);
        }
    }

    private void sliceProof(ActionEvent event) {
        if (extension.currentProof == null) {
            return;
        }
        analyzeProof(event);
        Proof p = extension.trackers.get(extension.currentProof).sliceProof();
        try {
            if (p != null) {
                // TODO: do this differently
                p.saveToFile(new File("/tmp/sliced.proof"));
                mediator.getUI().loadProblem(new File("/tmp/sliced.proof"));
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private void resetLabels() {
        totalSteps.setText("Total steps: ?");
        usefulSteps.setText("Useful steps: ?");
    }

    private void displayResults(AnalysisResults results) {
        totalSteps.setText("Total steps: " + results.totalSteps);
        usefulSteps.setText("Useful steps: " + results.usefulSteps);
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
}
