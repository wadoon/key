// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

/**
 * Dialog for instantiating holes left by lazy symbolic execution of a loop.
 *
 * @author Dominic Steinhöfel
 */
public class InstantiateLazyLoopHoleDialog extends JDialog {
    private static final long serialVersionUID = 1L;

    private final static MainWindow MAIN_WINDOW_INSTANCE = //
            MainWindow.getInstance();
    /** The initial size of this dialog. */
    private static final Dimension INITIAL_SIZE = new Dimension(900, 450);
    private static final Font TXT_AREA_FONT = //
            new Font(Font.MONOSPACED, Font.PLAIN, 14);

    private final JList<LoopHole> holesSelectionBox;
    private final JTabbedPane instantiationTabbedPane = new JTabbedPane();
    private final List<LoopHole> lastSelection = new ArrayList<>();

    public InstantiateLazyLoopHoleDialog() {
        super(MAIN_WINDOW_INSTANCE,
            "Instantiate Lazy Symbolic Execution Holes for Loops", true);
        setLocation(MAIN_WINDOW_INSTANCE.getLocation());
        setSize(INITIAL_SIZE);

        holesSelectionBox = new JList<>(retrieveLoopHoles());

        getContentPane().setLayout(new BorderLayout());

        getContentPane().add(setupLoopChoicePanel(), BorderLayout.NORTH);
        getContentPane().add(instantiationTabbedPane, BorderLayout.CENTER);
        getContentPane().add(setupButtons(), BorderLayout.SOUTH);

        holesSelectionBox.addListSelectionListener(new ListSelectionListener() {
            @Override
            public void valueChanged(ListSelectionEvent e) {
                final List<LoopHole> newSelection = //
                        holesSelectionBox.getSelectedValuesList().stream()
                                .filter(lh -> lh != null)
                                .collect(Collectors.toList());

                // Remove all those that are no longer selected
                final List<LoopHole> deselectedOnes = //
                        new ArrayList<>(lastSelection);
                deselectedOnes.removeAll(newSelection);

                for (final LoopHole deselected : deselectedOnes) {
                    instantiationTabbedPane.remove(instantiationTabbedPane
                            .indexOfTab(deselected.instTabTitle()));
                }

                for (final LoopHole selected : newSelection) {
                    if (lastSelection.contains(selected)) {
                        continue;
                    }

                    instantiationTabbedPane.addTab(selected.instTabTitle(),
                        createInstantiationPanelFor(selected));
                }

                lastSelection.clear();
                lastSelection.addAll(newSelection);
            }
        });
    }

    private Component setupButtons() {
        final JPanel result = new JPanel();
        result.setLayout(new FlowLayout(FlowLayout.CENTER));

        final JButton okButton = new JButton("OK");
        // okButton.setBorder(new EmptyBorder(0, 0, 0, 10));
        result.add(Box.createHorizontalStrut(10));

        final JButton cancelButton = new JButton("Cancel");
        cancelButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                InstantiateLazyLoopHoleDialog.this.setVisible(false);
            }
        });

        result.add(okButton);
        result.add(cancelButton);

        return result;
    }

    protected Component createInstantiationPanelFor(LoopHole selected) {
        final JPanel result = new JPanel();
        result.setLayout(new BoxLayout(result, BoxLayout.Y_AXIS));

        final JLabel lblInstPC = //
                new JLabel("Instantiation for path condition "
                        + selected.getPathCondPlaceholder());
        lblInstPC.setAlignmentX(Component.LEFT_ALIGNMENT);
        result.add(lblInstPC);
        result.add(Box.createRigidArea(new Dimension(0, 5)));

        final JTextArea txtPCInst = new JTextArea();
        txtPCInst.setFont(TXT_AREA_FONT);
        final JScrollPane scrTxtPCInst = new JScrollPane(txtPCInst);
        result.add(scrTxtPCInst);
        result.add(Box.createHorizontalGlue());
        result.add(Box.createRigidArea(new Dimension(0, 10)));
        scrTxtPCInst.setAlignmentX(Component.LEFT_ALIGNMENT);

        final JLabel lblInstSymbSt = //
                new JLabel("Instantiation for symbolic store "
                        + selected.getSymbStorePlaceholder());
        result.add(lblInstSymbSt);
        result.add(Box.createRigidArea(new Dimension(0, 5)));
        lblInstSymbSt.setAlignmentX(Component.LEFT_ALIGNMENT);

        final JTextArea txtSymbStInst = new JTextArea();
        txtSymbStInst.setFont(TXT_AREA_FONT);
        final JScrollPane scrTxtSymbStInst = new JScrollPane(txtSymbStInst);
        result.add(scrTxtSymbStInst);
        result.add(Box.createHorizontalGlue());
        scrTxtSymbStInst.setAlignmentX(Component.LEFT_ALIGNMENT);

        return result;
    }

    private JPanel setupLoopChoicePanel() {
        final JPanel result = new JPanel();
        result.setLayout(new BorderLayout());

        final TitledBorder title = BorderFactory
                .createTitledBorder("Select Holes to Fill");
        title.setTitleJustification(TitledBorder.LEFT);
        result.setBorder(title);

        holesSelectionBox.setSelectionMode(
            ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);
        holesSelectionBox.setVisibleRowCount(5);
        result.add(new JScrollPane(holesSelectionBox), BorderLayout.CENTER);

        return result;
    }

    private LoopHole[] retrieveLoopHoles() {
        // TODO Dummy Code
        final LoopHole[] result = new LoopHole[4];
        for (int i = 0; i < 3; i++) {
            result[i] = new LoopHole(i + 1, "C_sk_" + i, "U_sk_" + i);
        }
        return result;
    }

    private static class LoopHole {
        private final int loopNum;
        private final String pathCondPlaceholder;
        private final String symbStorePlaceholder;

        public LoopHole(int loopNum, String pathCondPlaceholder,
                String symbStorePlaceholder) {
            this.loopNum = loopNum;
            this.pathCondPlaceholder = pathCondPlaceholder;
            this.symbStorePlaceholder = symbStorePlaceholder;
        }

        public String getPathCondPlaceholder() {
            return pathCondPlaceholder;
        }

        public String getSymbStorePlaceholder() {
            return symbStorePlaceholder;
        }

        public String instTabTitle() {
            return "Loop " + loopNum;
        }

        @Override
        public String toString() {
            return String.format("Loop %d: (%s, %s)", loopNum,
                pathCondPlaceholder, symbStorePlaceholder);
        }
    }

    public static void main(String[] args) {
        new InstantiateLazyLoopHoleDialog().setVisible(true);
    }
}
