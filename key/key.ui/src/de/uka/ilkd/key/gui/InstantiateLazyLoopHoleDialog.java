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
import java.awt.Container;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Dialog for instantiating holes left by lazy symbolic execution of a loop.
 *
 * @author Dominic Steinhöfel
 */
public class InstantiateLazyLoopHoleDialog extends JDialog {
    private static final long serialVersionUID = 1L;

    /** The initial size of this dialog. */
    private static final Dimension INITIAL_SIZE = new Dimension(900, 450);
    private static final Font TXT_AREA_FONT = //
            new Font(Font.MONOSPACED, Font.PLAIN, 14);

    private final Proof proof;

    private boolean okPressed = false;
    private List<SingleResult> results;

    private final List<ParserProblem> problems = new ArrayList<>();
    private final List<Runnable> problemChangeListeners = new ArrayList<>();

    private final JList<LoopHole> holesSelectionBox;
    private final JTabbedPane instantiationTabbedPane = new JTabbedPane();
    private final List<LoopHole> lastSelection = new ArrayList<>();
    private final Map<LoopHole, JPanel> instantiationPanels = new HashMap<>();

    public InstantiateLazyLoopHoleDialog(MainWindow mainWindow, Proof proof) {
        super(mainWindow, "Instantiate Lazy Symbolic Execution Holes for Loops",
            true);
        if (mainWindow != null) {
            setLocation(mainWindow.getLocation());
        }
        setSize(INITIAL_SIZE);

        this.proof = proof;

        this.holesSelectionBox = new JList<>(retrieveLoopHoles());

        getContentPane().setLayout(new BorderLayout());

        getContentPane().add(setupLoopChoicePanel(), BorderLayout.NORTH);
        final JSplitPane centerPanel = new JSplitPane(
            JSplitPane.HORIZONTAL_SPLIT, instantiationTabbedPane,
            setupProblemsView());
        centerPanel.setResizeWeight(.6);
        getContentPane().add(centerPanel, BorderLayout.CENTER);
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
                    final int tabIdx = instantiationTabbedPane
                            .indexOfTab(deselected.instTabTitle());
                    if (tabIdx == -1) {
                        continue;
                    }
                    instantiationTabbedPane.remove(tabIdx);
                    final Optional<ParserProblem> maybeProblem = problems
                            .stream().filter(p -> p.loopHole.equals(deselected))
                            .findFirst();
                    problems.remove(maybeProblem.orElse(null));
                    informParserProblemChangeListeners();
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

    private Component setupProblemsView() {
        final JTextArea result = new JTextArea();
        final TitledBorder title = BorderFactory
                .createTitledBorder("Parser Problems");
        title.setTitleJustification(TitledBorder.LEFT);
        result.setBorder(title);
        result.setFont(TXT_AREA_FONT);
        result.setEditable(false);

        problemChangeListeners.add(() -> {
            final StringBuilder sb = new StringBuilder();

            for (ParserProblem problem : problems) {
                if (!problem.hasAProblem()) {
                    continue;
                }

                sb.append(problem.loopHole.toString())
                        .append("\n========================");

                if (problem.pathCondProblem.isPresent()) {
                    sb.append("\nPath Condition:\n")
                            .append(problem.pathCondProblem.get());
                }
                if (problem.symbStProblem.isPresent()) {
                    sb.append("\nSymbolic Store:\n")
                            .append(problem.symbStProblem.get());
                }

                sb.append("\n\n");
            }

            result.setText(sb.toString());
        });

        return new JScrollPane(result);
    }

    private boolean incompleteInput = false;

    private void collectResults() {
        final List<SingleResult> result = new ArrayList<>();
        incompleteInput = lastSelection.isEmpty();

        for (LoopHole lh : lastSelection) {
            final Container instPane = instantiationPanels.get(lh);

            final List<JTextArea> taComponents = getAllComponents(instPane)
                    .stream().filter(c -> c instanceof JTextArea)
                    .map(JTextArea.class::cast) //
                    .collect(Collectors.toList());
            final String pathCondInstText = taComponents.get(0).getText();
            final String symbStInstText = taComponents.get(1).getText();

            if (pathCondInstText.isEmpty() || symbStInstText.isEmpty()) {
                incompleteInput = true;
            }

            result.add(new SingleResult(lh, pathCondInstText, symbStInstText));
        }

        this.results = result;
    }

    private static List<Component> getAllComponents(final Container c) {
        Component[] comps = c.getComponents();
        List<Component> compList = new ArrayList<Component>();
        for (Component comp : comps) {
            compList.add(comp);
            if (comp instanceof Container) {
                compList.addAll(getAllComponents((Container) comp));
            }
        }
        return compList;
    }

    public List<SingleResult> getUserInput() {
        return results;
    }

    public boolean okPressed() {
        return okPressed;
    }

    private Component setupButtons() {
        final JPanel result = new JPanel();
        result.setLayout(new FlowLayout(FlowLayout.CENTER));

        final JButton okButton = new JButton("OK");
        problemChangeListeners.add(() -> {
            okButton.setEnabled(
                !problems.stream().anyMatch(p -> p.hasAProblem()));
        });
        okButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                collectResults();
                if (incompleteInput) {
                    JOptionPane.showMessageDialog(
                        InstantiateLazyLoopHoleDialog.this,
                        "You left some input fields empty. Please fill in"
                                + " all the placeholder instantiations for"
                                + " all selected loop holes.",
                        "Incomplete Input", JOptionPane.ERROR_MESSAGE);
                } else {
                    okPressed = true;
                    InstantiateLazyLoopHoleDialog.this.setVisible(false);
                }
            }
        });
        result.add(Box.createHorizontalStrut(10));

        final JButton cancelButton = new JButton("Cancel");
        cancelButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                okPressed = false;
                InstantiateLazyLoopHoleDialog.this.setVisible(false);
            }
        });

        result.add(okButton);
        result.add(cancelButton);

        return result;
    }

    private Component createInstantiationPanelFor(final LoopHole selected) {
        if (instantiationPanels.containsKey(selected)) {
            return instantiationPanels.get(selected);
        }

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

        txtPCInst.addKeyListener(new KeyAdapter() {
            @Override
            public void keyReleased(KeyEvent e) {
                final ParserProblem pp = getParserProblemObjectFor(selected);
                if (txtPCInst.getText().isEmpty()) {
                    pp.setPathCondProblem(null);
                    return;
                }

                final DefaultTermParser parser = new DefaultTermParser();
                try {
                    parser.parse(new StringReader(txtPCInst.getText()),
                        Sort.FORMULA, proof.getServices(),
                        proof.getServices().getNamespaces(),
                        proof.abbreviations());
                    pp.setPathCondProblem(null);
                } catch (ParserException e1) {
                    pp.setPathCondProblem(e1.getLocalizedMessage());
                }
            }
        });

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

        txtSymbStInst.addKeyListener(new KeyAdapter() {
            @Override
            public void keyReleased(KeyEvent e) {
                final ParserProblem pp = getParserProblemObjectFor(selected);
                if (txtSymbStInst.getText().isEmpty()) {
                    pp.setSymbStoreProblem(null);
                    return;
                }

                final DefaultTermParser parser = new DefaultTermParser();
                try {
                    parser.parse(new StringReader(txtSymbStInst.getText()),
                        Sort.UPDATE, proof.getServices(),
                        proof.getServices().getNamespaces(),
                        proof.abbreviations());
                    pp.setSymbStoreProblem(null);
                } catch (ParserException e1) {
                    pp.setSymbStoreProblem(e1.getLocalizedMessage());
                }
            }
        });

        instantiationPanels.put(selected, result);
        return result;
    }

    private ParserProblem getParserProblemObjectFor(LoopHole lh) {
        Optional<ParserProblem> maybeProblem = problems.stream()
                .filter(p -> p.loopHole.equals(lh)).findFirst();

        if (!maybeProblem.isPresent()) {
            maybeProblem = Optional.of(new ParserProblem(lh));
            problems.add(maybeProblem.get());
        }

        return maybeProblem.get();
    }

    private Component setupLoopChoicePanel() {
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
        if (proof == null) {
            /* For GUI design purposes */
            return mockupRetrieveLoopHoles();
        }

        final Iterable<Node> nodes = () -> proof.root().subtreeIterator();
        final List<RuleApp> lazyLoopRules = //
                StreamSupport.stream(nodes.spliterator(), false)
                        .map(Node::getAppliedRuleApp) //
                        .filter(ra -> ra != null) //
                        .filter(ra -> ra.rule().name().toString()
                                .equals("lazyLoop"))
                        .collect(Collectors.toList());

        final LoopHole[] result = new LoopHole[lazyLoopRules.size()];
        for (int i = 0; i < result.length; i++) {
            final SVInstantiations instantiations = //
                    ((PosTacletApp) lazyLoopRules.get(i)).instantiations();
            final String pcPlaceholderName = instantiations
                    .lookupValue(new Name("C_sk")).toString();
            final String symbStPlaceholderName = instantiations
                    .lookupValue(new Name("U_sk")).toString();
            result[i] = new LoopHole(i + 1, pcPlaceholderName,
                symbStPlaceholderName);
        }

        return result;
    }

    private void informParserProblemChangeListeners() {
        problemChangeListeners.forEach(l -> l.run());
    }

    private LoopHole[] mockupRetrieveLoopHoles() {
        final LoopHole[] result = new LoopHole[4];
        for (int i = 0; i < 3; i++) {
            result[i] = new LoopHole(i + 1, "C_sk_" + i, "U_sk_" + i);
        }
        return result;
    }

    public static class SingleResult {
        private final LoopHole loopHole;
        private final String pathCondInst;
        private final String symbStoreInst;

        public SingleResult(LoopHole loopHole, String pathCondInst,
                String symbStoreInst) {
            this.loopHole = loopHole;
            this.pathCondInst = pathCondInst;
            this.symbStoreInst = symbStoreInst;
        }

        public LoopHole getLoopHole() {
            return loopHole;
        }

        public String getPathCondInst() {
            return pathCondInst;
        }

        public String getSymbStoreInst() {
            return symbStoreInst;
        }
    }

    private class ParserProblem {
        private LoopHole loopHole;
        private Optional<String> pathCondProblem = Optional.empty();
        private Optional<String> symbStProblem = Optional.empty();

        public ParserProblem(LoopHole loopHole) {
            this.loopHole = loopHole;
        }

        public void setPathCondProblem(String pathCondProblem) {
            this.pathCondProblem = Optional.ofNullable(pathCondProblem);
            informParserProblemChangeListeners();
        }

        public void setSymbStoreProblem(String symbStProblem) {
            this.symbStProblem = Optional.ofNullable(symbStProblem);
            informParserProblemChangeListeners();
        }

        public boolean hasAProblem() {
            return pathCondProblem.isPresent() || symbStProblem.isPresent();
        }
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
        new InstantiateLazyLoopHoleDialog(null, null).setVisible(true);
    }
}
