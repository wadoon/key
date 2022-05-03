// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package org.key_project.slicing;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.MainWindowTabbedPane;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Proof;

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

    private MainWindow mainWindow;
    private KeYMediator mediator;
    private SlicingExtension extension;
    private JLabel totalSteps;
    private JLabel usefulSteps;

    public SlicingLeftPanel(MainWindow window, KeYMediator mediator, SlicingExtension extension) {
        super();

        setName("slicingPane");

        setLayout(new GridBagLayout());

        var panel = new JPanel();
        panel.setLayout(new BoxLayout(panel, BoxLayout.Y_AXIS));
        panel.setBorder(new TitledBorder("Dependency analysis"));

        var button = new JButton("Export .dot");
        button.addActionListener(e -> exportDot(e));
        var button2 = new JButton("View formula graph");
        button2.addActionListener(e -> previewGraph(e));
        var button3 = new JButton("Run analysis");
        button3.addActionListener(e -> analyzeProof(e));
        var button4 = new JButton("Slice proof");
        button4.addActionListener(e -> sliceProof(e));
        totalSteps = new JLabel();
        usefulSteps = new JLabel();
        resetLabels();
        panel.add(totalSteps);
        panel.add(usefulSteps);
        panel.add(button3);
        GridBagConstraints c = new GridBagConstraints();
        c.gridx = 0;
        c.gridy = 0;
        c.fill = GridBagConstraints.HORIZONTAL;
        c.weightx = 1.0;
        c.weighty = 0.0;
        c.anchor = GridBagConstraints.PAGE_START;
        add(panel, c);
        c = new GridBagConstraints();
        c.gridx = 0;
        c.gridy = 1;
        c.weighty = 0.0;
        c.anchor = GridBagConstraints.FIRST_LINE_START;
        add(button, c);
        c = new GridBagConstraints();
        c.gridx = 0;
        c.gridy = 2;
        c.weighty = 0.0;
        c.anchor = GridBagConstraints.FIRST_LINE_START;
        add(button2, c);
        c = new GridBagConstraints();
        c.gridx = 0;
        c.gridy = 3;
        c.weighty = 1.0;
        c.anchor = GridBagConstraints.FIRST_LINE_START;
        add(button4, c);
        invalidate();

        this.mainWindow = window;
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
                String text = extension.trackers.get(currentProof).exportDot();
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
        if (tracker.analysisResults != null) {
            displayResults(tracker.analysisResults);
        }
    }

    private void previewGraph(ActionEvent e) {
        if (extension.currentProof == null || extension.currentProof.countNodes() < 2) {
            return;
        }
        String text = extension.trackers.get(extension.currentProof).exportDot();
        var preview = new PreviewDialog(SwingUtilities.getWindowAncestor((JComponent) e.getSource()), text);
    }

    private void analyzeProof(ActionEvent e) {
        if (extension.currentProof == null) {
            return;
        }
        var results = extension.trackers.get(extension.currentProof).analyze((JComponent) e.getSource());
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

    @Override
    public String getTitle() {
        return "Proof Slicing";
    }

    @Override
    public Icon getIcon() {
        return INFO_ICON;
    }

    @Override
    public JComponent getComponent() {
        return this;
    }
}
