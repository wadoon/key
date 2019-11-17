// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.gui.abstractexecution.relational.dialogs;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.regex.Pattern;

import javax.swing.BorderFactory;
import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.SwingUtilities;
import javax.swing.event.ListDataEvent;
import javax.swing.event.ListDataListener;
import javax.xml.bind.JAXBException;

import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.SyntaxConstants;
import org.fife.ui.rtextarea.RTextScrollPane;
import org.xml.sax.SAXException;

import de.uka.ilkd.key.abstractexecution.relational.model.AERelationalModel;
import de.uka.ilkd.key.abstractexecution.relational.model.AbstractLocsetDeclaration;
import de.uka.ilkd.key.abstractexecution.relational.model.NullarySymbolDeclaration;
import de.uka.ilkd.key.abstractexecution.relational.model.PredicateDeclaration;
import de.uka.ilkd.key.abstractexecution.relational.model.ProgramVariableDeclaration;
import de.uka.ilkd.key.abstractexecution.relational.model.ProofBundleConverter;
import de.uka.ilkd.key.abstractexecution.relational.model.ProofBundleConverter.BundleSaveResult;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.abstractexecution.relational.components.FormulaInputTextArea;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * 
 * @author Dominic Steinhoefel
 */
public class AERelationalDialog extends JDialog {
    private static final String DUMMY_KEY_FILE = "/de/uka/ilkd/key/gui/abstractexecution/relational/dummy.key";
    private static final String TITLE = "Relational Proofs with Abstract Execution";
    private static final String PROOF_BUNDLE_ENDING = ".zproof";
    private static final String STD_POSTCONDREL_TOOLTIP = "Relation between values of the relevant locations after execution.<br/>"
            + "You may use the keywords \"\\result_1\" and \"\\result_2\" to access<br/>"
            + "the respective result arrays.<br/>"
            + "Access individual values with \"\\result_1[0]\" etc. Use type casts<br/>"
            + "in non-trivial compound expressions.";

    private static final long serialVersionUID = 1L;

    private AERelationalModel model;
    private MainWindow mainWindow;
    private Services services = null;
    // NOTE: Only access via setReadonly / isReadonly!
    private boolean readonly = false;

    private final DefaultListModel<AbstractLocsetDeclaration> locsetDeclsListModel = new DefaultListModel<>();
    private final DefaultListModel<PredicateDeclaration> predDeclsListModel = new DefaultListModel<>();
    private final DefaultListModel<ProgramVariableDeclaration> progVarDeclsListModel = new DefaultListModel<>();
    private final DefaultListModel<NullarySymbolDeclaration> relevantSymbolsOneListModel = new DefaultListModel<>();
    private final DefaultListModel<NullarySymbolDeclaration> relevantSymbolsTwoListModel = new DefaultListModel<>();

    private final RSyntaxTextArea codeLeft = new RSyntaxTextArea(20, 60);
    private final RSyntaxTextArea codeRight = new RSyntaxTextArea(20, 60);
    private final FormulaInputTextArea resultRelationText = new FormulaInputTextArea(
            STD_POSTCONDREL_TOOLTIP, formula -> {
                // Replacement of special placeholders for result sequences
                String result = formula;
                result = result.replaceAll(Pattern.quote(ProofBundleConverter.RESULT_1),
                        ProofBundleConverter.RES1);
                result = result.replaceAll(Pattern.quote(ProofBundleConverter.RESULT_2),
                        ProofBundleConverter.RES2);
                return result;
            });

    private final List<ServicesLoadedListener> servicesLoadedListeners = new ArrayList<>();
    private final List<ProgramVariablesChangedListener> programVariablesChangedListeners = new ArrayList<>();
    private final List<ReadonlyListener> readOnlyListeners = new ArrayList<>();

    public static void main(String[] args) {
        final AERelationalModel model = AERelationalModel.EMPTY_MODEL;
        final AERelationalDialog dia = new AERelationalDialog(null, model);
        dia.setVisible(true);
    }

    public AERelationalDialog(MainWindow mainWindow, AERelationalModel model) {
        super(mainWindow, false);

        assert model != null;
        this.model = model;
        this.mainWindow = mainWindow;

        setTitle(TITLE);
        setIconImage(IconFontSwing.buildImage(FontAwesomeSolid.BALANCE_SCALE, 16, Color.BLACK));

        // We want to ask whether model should be saved
        setDefaultCloseOperation(DO_NOTHING_ON_CLOSE);

        final JPanel contentPanel = new JPanel(new BorderLayout());
        getContentPane().setLayout(new BorderLayout());
        getContentPane().add(contentPanel, BorderLayout.CENTER);

        final JPanel declarationsContainer = createDeclarationsContainer();
        final JPanel programViewContainer = createProgramViewContainer();
        final JPanel postconditionContainer = createPostconditionContainer();

        final JSplitPane splitPane1 = new JSplitPane( //
                JSplitPane.HORIZONTAL_SPLIT, declarationsContainer, programViewContainer);
        splitPane1.setResizeWeight(0);
        splitPane1.setOneTouchExpandable(true);

        final JSplitPane splitPane2 = new JSplitPane(//
                JSplitPane.HORIZONTAL_SPLIT, splitPane1, postconditionContainer);
        splitPane2.setResizeWeight(1);
        splitPane2.setOneTouchExpandable(true);
        contentPanel.add(splitPane2, BorderLayout.CENTER);

        final JPanel ctrlPanel = createControlPanel();
        contentPanel.add(ctrlPanel, BorderLayout.SOUTH);

        getAllComponents(contentPanel).stream().filter(JButton.class::isInstance)
                .map(JButton.class::cast).forEach(btn -> btn.setBackground(Color.WHITE));

        final int preferredWidth = programViewContainer.getPreferredSize().width
                + declarationsContainer.getPreferredSize().width
                + postconditionContainer.getPreferredSize().width + 10;

        setPreferredSize(new Dimension(preferredWidth, 700));
        pack();

        loadFromModel();
        installListeners();

        new Thread(() -> {
            initializeServices();
        }).start();

    }

    public void installListeners() {
        readOnlyListeners.add(ro -> {
            if (ro) {
                setTitle(String.format("%s (READ ONLY - Save to edit)", TITLE));
            } else {
                setTitle(TITLE);
            }
        });

        servicesLoadedListeners.add(() -> {
            model.getAbstractLocationSets().forEach(loc -> {
                try {
                    LocsetInputDialog.checkAndRegister(loc, services);
                } catch (ParserException e) {
                    // Shouldn't happen! Already saved!
                    e.printStackTrace();
                }
            });

            model.getProgramVariableDeclarations().forEach(pv -> {
                ProgramVariableInputDialog.checkAndRegister(pv, services);
            });

            model.getPredicateDeclarations().forEach(pred -> {
                try {
                    PredicateInputDialog.checkAndRegister(pred, services);
                } catch (ParserException e) {
                    // Shouldn't happen! Already saved!
                    e.printStackTrace();
                }
            });
        });

        servicesLoadedListeners.add(() -> {
            // Add special result symbols
            final Namespace<Function> functions = services.getNamespaces().functions();
            final Sort seqSort = services.getTypeConverter().getSeqLDT().targetSort();
            functions.add(new Function(new Name(ProofBundleConverter.RES1), seqSort));
            functions.add(new Function(new Name(ProofBundleConverter.RES2), seqSort));
        });

        addWindowListener(new WindowAdapter() {
            @Override
            public void windowClosing(WindowEvent e) {
                final int answer = JOptionPane.showConfirmDialog(AERelationalDialog.this,
                        "Do you want to save your model before closing?", "Save Model",
                        JOptionPane.YES_NO_OPTION, JOptionPane.QUESTION_MESSAGE);

                if (answer == JOptionPane.YES_OPTION) {
                    try {
                        if (saveModelToFile()) {
                            setVisible(false);
                            dispose();
                        }
                    } catch (IOException | JAXBException exc) {
                        JOptionPane.showMessageDialog(AERelationalDialog.this,
                                "<html>Could not save model to file.<br><br/>Message:<br/>"
                                        + exc.getMessage() + "</html>",
                                "Problem Saving Model", JOptionPane.ERROR_MESSAGE);
                        return;
                    }
                } else if (answer == JOptionPane.NO_OPTION) {
                    setVisible(false);
                    dispose();
                }
            }
        });
    }

    /**
     * Prevents changes to the model iff readonly is set to true. Changes are
     * automatically allowed again when the model is saved to another location.
     * 
     * @param readonly The readonly flag.
     */
    public void setReadonly(boolean readonly) {
        this.readonly = readonly;
        readOnlyListeners.forEach(l -> l.readonlyChanged(readonly));
    }

    public boolean isReadonly() {
        return readonly;
    }

    private void initializeServices() {
        KeYEnvironment<?> environment = null;
        try {
            final InputStream is = AERelationalDialog.class.getResourceAsStream(DUMMY_KEY_FILE);

            if (is == null) {
                SwingUtilities.invokeLater(() -> {
                    JOptionPane.showMessageDialog(AERelationalDialog.this,
                            "Ooops... Could not load resource file!",
                            "Problem During Initialization", JOptionPane.ERROR_MESSAGE);
                });
                return;
            }

            final Path tempFilePath = Files.createTempFile("dummy_", ".key");
            final File tempFile = tempFilePath.toFile();
            tempFile.deleteOnExit();
            Files.copy(is, tempFilePath, StandardCopyOption.REPLACE_EXISTING);
            environment = KeYEnvironment.load( //
                    JavaProfile.getDefaultInstance(), tempFile, null, null, null, true);
        } catch (ProblemLoaderException | IOException e) {
            SwingUtilities.invokeLater(() -> {
                JOptionPane.showMessageDialog(AERelationalDialog.this,
                        "<html>Ooops... Could not initialize proof services!<br/><br/>Message:<br/>"
                                + e.getMessage() + "</html>",
                        "Problem During Initialization", JOptionPane.ERROR_MESSAGE);
            });
            return;
        }

        final KeYEnvironment<?> env = environment;
        SwingUtilities.invokeLater(() -> {
            this.services = env.getLoadedProof().getServices();
            servicesLoadedListeners.forEach(ServicesLoadedListener::servicesLoaded);
        });
    }

    private void loadFromModel() {
        codeLeft.setText(model.getProgramOne());
        codeRight.setText(model.getProgramTwo());
        resultRelationText.setText(model.getPostCondition());

        locsetDeclsListModel.clear();
        model.getAbstractLocationSets().forEach(locsetDeclsListModel::addElement);
        predDeclsListModel.clear();
        model.getPredicateDeclarations().forEach(predDeclsListModel::addElement);
        progVarDeclsListModel.clear();
        model.getProgramVariableDeclarations().forEach(progVarDeclsListModel::addElement);
        relevantSymbolsOneListModel.clear();
        model.getRelevantVarsOne().forEach(relevantSymbolsOneListModel::addElement);
        relevantSymbolsTwoListModel.clear();
        model.getRelevantVarsOne().forEach(relevantSymbolsTwoListModel::addElement);
    }

    private void updateModel() {
        model.setProgramOne(codeLeft.getText());
        model.setProgramTwo(codeRight.getText());
        model.setPostCondition(resultRelationText.getText());
        model.setAbstractLocationSets(Collections.list(locsetDeclsListModel.elements()));
        model.setPredicateDeclarations(Collections.list(predDeclsListModel.elements()));
        model.setProgramVariableDeclarations(Collections.list(progVarDeclsListModel.elements()));
        model.setRelevantVarsOne(Collections.list(relevantSymbolsOneListModel.elements()));
        model.setRelevantVarsTwo(Collections.list(relevantSymbolsTwoListModel.elements()));
    }

    private boolean saveModelToFile() throws IOException, JAXBException {
        final KeYFileChooser chooser = KeYFileChooser
                .getFileChooser("Choose Destination for AE-Relational Model");

        final boolean saveResult = model.getFile()
                .map(f -> chooser.showSaveDialog(AERelationalDialog.this, f))
                .orElseGet(() -> chooser.showSaveDialog(AERelationalDialog.this, null, ".aer"));
        if (saveResult) {
            return saveModelToFile(chooser.getSelectedFile());
        } else {
            return false;
        }
    }

    private boolean saveModelToFile(File file) throws IOException, JAXBException {
        updateModel();

        if (model.getFile().map(oldFile -> !file.equals(oldFile)).orElse(true)) {
            setReadonly(false);
        }

        Files.write(file.toPath(), model.toXml().getBytes());
        model.setFile(file);
        return true;
    }

    private void loadFromFile() throws IOException, JAXBException, SAXException {
        final KeYFileChooser chooser = KeYFileChooser
                .getFileChooser("Choose AE-Relational Model File");

        if (chooser.showOpenDialog(this)) {
            final File file = chooser.getSelectedFile();

            if (!file.getName().endsWith(".aer")) {
                JOptionPane.showMessageDialog(AERelationalDialog.this,
                        "No AE-Relational File (.aer)", "Problem Loading Model",
                        JOptionPane.ERROR_MESSAGE);
                return;
            }

            model = AERelationalModel.fromXml(new String(Files.readAllBytes(file.toPath())));
            model.setFile(file);
            loadFromModel();
        }
    }

    private JPanel createControlPanel() {
        final JButton loadFromFileBtn = new JButton("Load Model",
                IconFontSwing.buildIcon(FontAwesomeSolid.FILE_UPLOAD, 16, Color.BLACK));
        loadFromFileBtn
                .setPreferredSize(new Dimension(loadFromFileBtn.getPreferredSize().width, 30));
        loadFromFileBtn.addActionListener(e -> {
            try {
                loadFromFile();
            } catch (IOException | JAXBException exc) {
                JOptionPane.showMessageDialog(AERelationalDialog.this,
                        "<html>Could not load model from file.<br><br/>Message:<br/>"
                                + exc.getMessage() + "</html>",
                        "Problem Loading Model", JOptionPane.ERROR_MESSAGE);
            } catch (SAXException exc) {
                JOptionPane.showMessageDialog(AERelationalDialog.this,
                        "<html>Could not load model from file: XML Schema violated.<br><br/>Message:<br/>"
                                + exc.getMessage() + "</html>",
                        "Problem Loading Model", JOptionPane.ERROR_MESSAGE);
            }
        });

        final JButton saveToFileBtn = new JButton("Save Model",
                IconFontSwing.buildIcon(FontAwesomeSolid.FILE_DOWNLOAD, 16, Color.BLACK));
        saveToFileBtn.setPreferredSize(new Dimension(saveToFileBtn.getPreferredSize().width, 30));
        saveToFileBtn.addActionListener(e -> {
            try {
                saveModelToFile();
            } catch (IOException | JAXBException exc) {
                JOptionPane.showMessageDialog(AERelationalDialog.this,
                        "<html>Could not save model to file.<br><br/>Message:<br/>"
                                + exc.getMessage() + "</html>",
                        "Problem Saving Model", JOptionPane.ERROR_MESSAGE);
            }
        });

        final JButton saveBundleAndStartBtn = new JButton("Start Proof",
                IconFontSwing.buildIcon(FontAwesomeSolid.PLAY, 16, Color.BLACK));
        saveBundleAndStartBtn.setPreferredSize(
                new Dimension(saveBundleAndStartBtn.getPreferredSize().width, 30));
        saveBundleAndStartBtn.addActionListener(e -> createAndLoadBundle());

        final JPanel ctrlPanel = new JPanel(new FlowLayout(FlowLayout.CENTER));
        ctrlPanel.add(loadFromFileBtn);
        ctrlPanel.add(saveToFileBtn);
        ctrlPanel.add(saveBundleAndStartBtn);

        return ctrlPanel;
    }

    private void createAndLoadBundle() {
        updateModel();

        try {
            final String tmpFilePrefix = model.getFile().map(File::getName)
                    .orElse("AERelationalModel") + "_";
            final File proofBundleFile = Files.createTempFile( //
                    tmpFilePrefix, PROOF_BUNDLE_ENDING).toFile();
            final BundleSaveResult result = new ProofBundleConverter(model).save(proofBundleFile);
            mainWindow.loadProofFromBundle(result.getFile(), result.getProofPath().toFile());
        } catch (IOException | IllegalStateException e) {
            JOptionPane
                    .showMessageDialog(AERelationalDialog.this,
                            "<html>Problem saving proof bundle.<br/><br/>Message:<br/>"
                                    + e.getMessage() + "</html>",
                            "Problem Starting Proof", JOptionPane.ERROR_MESSAGE);
        }
    }

    private JPanel createProgramViewContainer() {
        final JPanel editorsContainer = new JPanel(new GridLayout(1, 2));
        final JComponent programOneView = createJavaEditorViewLeft();
        final JComponent programTwoView = createJavaEditorViewRight();
        editorsContainer.add(programOneView);
        editorsContainer.add(programTwoView);
        editorsContainer.setMinimumSize(new Dimension(600, 100));
        return editorsContainer;
    }

    private JPanel createPostconditionContainer() {
        final JPanel result = new JPanel(new GridLayout(3, 1));
        result.setBorder(BorderFactory.createEmptyBorder(0, 10, 10, 10));
        result.setPreferredSize(new Dimension(200, 0));
        result.setMinimumSize(new Dimension(200, 0));

        result.add(createRelevantLocationsOneContainer());
        result.add(createRelevantLocationsTwoContainer());
        result.add(createResultRelationView());

        return result;
    }

    private JPanel createRelevantLocationsOneContainer() {
        return createRelevantLocationsContainer("Relevant Locations (Left)",
                relevantSymbolsOneListModel, AERelationalModel::getRelevantVarsOne);
    }

    private JPanel createRelevantLocationsTwoContainer() {
        return createRelevantLocationsContainer("Relevant Locations (Right)",
                relevantSymbolsTwoListModel, AERelationalModel::getRelevantVarsTwo);
    }

    private JPanel createRelevantLocationsContainer(String labelText,
            DefaultListModel<NullarySymbolDeclaration> relevantSymbolsModel,
            java.util.function.Function<AERelationalModel, List<NullarySymbolDeclaration>> chosenRelevantSymbolsGetter) {
        final JPanel result = new JPanel(new BorderLayout());

        final JLabel titleLabel = new JLabel(labelText);
        final JPanel titleLabelContainer = new JPanel(new FlowLayout(FlowLayout.CENTER));
        titleLabelContainer.add(titleLabel);
        result.add(titleLabelContainer, BorderLayout.NORTH);

        final JList<NullarySymbolDeclaration> relevantSymbolsList = new JList<>();
        final JScrollPane scrollPane = new JScrollPane();
        scrollPane.setViewportView(relevantSymbolsList);
        result.add(scrollPane, BorderLayout.CENTER);

        relevantSymbolsList.setModel(relevantSymbolsModel);

        final JButton plusButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.PLUS, 16, Color.BLACK));
        plusButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                updateModel();
                final List<NullarySymbolDeclaration> allSymbols = new ArrayList<>();
                allSymbols.addAll(model.getProgramVariableDeclarations());
                allSymbols.addAll(model.getAbstractLocationSets());
                allSymbols.removeAll(chosenRelevantSymbolsGetter.apply(model));

                if (!allSymbols.isEmpty()) {
                    final NullarySymbolDeclaration chosen = (NullarySymbolDeclaration) JOptionPane
                            .showInputDialog(mainWindow, "Please choose a relevant location to add",
                                    "Add Relevant Location", JOptionPane.QUESTION_MESSAGE, null,
                                    allSymbols.toArray(new NullarySymbolDeclaration[0]),
                                    allSymbols.get(0));
                    relevantSymbolsModel.addElement(chosen);
                }
            }
        });

        final JButton minusButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.MINUS, 16, Color.BLACK));
        minusButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                for (int idx : relevantSymbolsList.getSelectedIndices()) {
                    relevantSymbolsModel.remove(idx);
                }
            }
        });

        plusButton.setEnabled(true);
        minusButton.setEnabled(true);

        this.readOnlyListeners.add(ro -> {
            plusButton.setEnabled(!ro);
            minusButton.setEnabled(!ro);
        });

        final JPanel buttonsPanel = new JPanel(new FlowLayout(FlowLayout.CENTER));
        buttonsPanel.add(plusButton);
        buttonsPanel.add(minusButton);

        result.add(buttonsPanel, BorderLayout.SOUTH);
        return result;
    }

    private JPanel createDeclarationsContainer() {
        final JPanel symbolDeclContainer = new JPanel(new GridLayout(3, 1));
        symbolDeclContainer.setBorder(BorderFactory.createEmptyBorder(0, 10, 10, 10));
        symbolDeclContainer.setPreferredSize(new Dimension(200, 0));
        symbolDeclContainer.setMinimumSize(new Dimension(200, 0));

        final JComponent programVariableDeclarations = createProgramVariableDeclarationsView();
        final JComponent locsetsDeclarations = createLocsetsDeclarationsView();
        final JComponent formulaDeclarations = createPredicatesDeclarationsView();

        programVariableDeclarations.setBorder(BorderFactory.createEmptyBorder(0, 0, 5, 0));
        locsetsDeclarations.setBorder(BorderFactory.createEmptyBorder(5, 0, 5, 0));
        formulaDeclarations.setBorder(BorderFactory.createEmptyBorder(5, 0, 5, 0));

        symbolDeclContainer.add(programVariableDeclarations);
        symbolDeclContainer.add(locsetsDeclarations);
        symbolDeclContainer.add(formulaDeclarations);

        return symbolDeclContainer;
    }

    private JPanel createResultRelationView() {
        final JPanel postCondContainer = new JPanel(new BorderLayout());
        postCondContainer.setBorder(BorderFactory.createEmptyBorder(5, 0, 0, 0));

        final JLabel titleLabel = new JLabel("Relation to Verify");
        final JPanel titleLabelContainer = new JPanel(new FlowLayout(FlowLayout.CENTER));
        titleLabelContainer.add(titleLabel);
        postCondContainer.add(titleLabelContainer, BorderLayout.NORTH);

        resultRelationText.setBorder(BorderFactory.createEtchedBorder());
        resultRelationText.setEnabled(false);
        resultRelationText.setBorder(BorderFactory.createCompoundBorder(
                resultRelationText.getBorder(), BorderFactory.createEmptyBorder(5, 5, 5, 5)));

        servicesLoadedListeners.add(() -> {
            resultRelationText.setServices(services);
            if (!isReadonly()) {
                resultRelationText.setEnabled(true);
            }
        });
        readOnlyListeners.add(ro -> {
            if (ro) {
                resultRelationText.setEnabled(false);
            } else if (services != null) {
                resultRelationText.setEnabled(true);
            }
        });

        postCondContainer.add(resultRelationText, BorderLayout.CENTER);
        return postCondContainer;
    }

    private JComponent createPredicatesDeclarationsView() {
        final JPanel result = new JPanel(new BorderLayout());

        final JLabel titleLabel = new JLabel("Abstract Predicates");
        final JPanel titleLabelContainer = new JPanel(new FlowLayout(FlowLayout.CENTER));
        titleLabelContainer.add(titleLabel);
        result.add(titleLabelContainer, BorderLayout.NORTH);

        final JList<PredicateDeclaration> predDeclsList = new JList<>();
        final JScrollPane scrollPane = new JScrollPane();
        scrollPane.setViewportView(predDeclsList);
        result.add(scrollPane, BorderLayout.CENTER);
        predDeclsList.setModel(predDeclsListModel);

        final JButton plusButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.PLUS, 16, Color.BLACK));
        plusButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                final PredicateDeclaration pd = PredicateInputDialog
                        .showInputDialog(AERelationalDialog.this, services);
                if (pd != null) {
                    predDeclsListModel.addElement(pd);
                }
            }
        });

        final JButton editButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.PEN, 16, Color.BLACK));
        editButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                if (predDeclsList.getSelectedIndices().length == 1) {
                    final PredicateDeclaration selectedElem = predDeclsList.getSelectedValue();
                    final PredicateDeclaration pd = PredicateInputDialog
                            .showInputDialog(AERelationalDialog.this, selectedElem, services);
                    if (pd != null) {
                        predDeclsListModel.set(predDeclsList.getSelectedIndex(), pd);
                    }
                }
            }
        });

        final JButton minusButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.MINUS, 16, Color.BLACK));
        minusButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                for (int idx : predDeclsList.getSelectedIndices()) {
                    predDeclsListModel.remove(idx);
                }
            }
        });

        plusButton.setEnabled(false);
        minusButton.setEnabled(false);
        editButton.setEnabled(false);

        this.servicesLoadedListeners.add(() -> {
            if (!isReadonly()) {
                plusButton.setEnabled(true);
                minusButton.setEnabled(true);
                editButton.setEnabled(true);
            }
        });
        this.readOnlyListeners.add(ro -> {
            if (ro) {
                plusButton.setEnabled(false);
                minusButton.setEnabled(false);
                editButton.setEnabled(false);
            } else if (services != null) {
                plusButton.setEnabled(true);
                minusButton.setEnabled(true);
                editButton.setEnabled(true);
            }
        });

        final JPanel buttonsPanel = new JPanel(new FlowLayout(FlowLayout.CENTER));
        buttonsPanel.add(plusButton);
        buttonsPanel.add(editButton);
        buttonsPanel.add(minusButton);

        result.add(buttonsPanel, BorderLayout.SOUTH);
        return result;
    }

    private JComponent createProgramVariableDeclarationsView() {
        final JPanel result = new JPanel(new BorderLayout());

        final JLabel titleLabel = new JLabel("Free Program Variables");
        final JPanel titleLabelContainer = new JPanel(new FlowLayout(FlowLayout.CENTER));
        titleLabelContainer.add(titleLabel);
        result.add(titleLabelContainer, BorderLayout.NORTH);

        final JList<ProgramVariableDeclaration> predDeclsList = new JList<>();
        final JScrollPane scrollPane = new JScrollPane();
        scrollPane.setViewportView(predDeclsList);
        result.add(scrollPane, BorderLayout.CENTER);
        predDeclsList.setModel(progVarDeclsListModel);
        progVarDeclsListModel.addListDataListener(new UniformListDataListener() {
            @Override
            public void listChanged(ListDataEvent e) {
                programVariablesChangedListeners.forEach(l -> l.programVariablesChanged(
                        Collections.list(progVarDeclsListModel.elements())));
            }
        });

        final JButton plusButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.PLUS, 16, Color.BLACK));
        plusButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                final ProgramVariableDeclaration pd = ProgramVariableInputDialog
                        .showInputDialog(AERelationalDialog.this, services);
                if (pd != null) {
                    progVarDeclsListModel.addElement(pd);
                }
            }
        });

        final JButton editButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.PEN, 16, Color.BLACK));
        editButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                if (predDeclsList.getSelectedIndices().length == 1) {
                    final ProgramVariableDeclaration selectedElem = predDeclsList
                            .getSelectedValue();
                    final ProgramVariableDeclaration pd = ProgramVariableInputDialog
                            .showInputDialog(AERelationalDialog.this, selectedElem, services);
                    if (pd != null) {
                        progVarDeclsListModel.set(predDeclsList.getSelectedIndex(), pd);
                    }
                }
            }
        });

        final JButton minusButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.MINUS, 16, Color.BLACK));
        minusButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                for (int idx : predDeclsList.getSelectedIndices()) {
                    final ProgramVariableDeclaration removed = progVarDeclsListModel.remove(idx);
                    services.getNamespaces().programVariables()
                            .remove(new Name(removed.getVarName()));
                }
            }
        });

        plusButton.setEnabled(false);
        minusButton.setEnabled(false);
        editButton.setEnabled(false);

        this.servicesLoadedListeners.add(() -> {
            if (!isReadonly()) {
                plusButton.setEnabled(true);
                minusButton.setEnabled(true);
                editButton.setEnabled(true);
            }
        });
        this.readOnlyListeners.add(ro -> {
            if (ro) {
                plusButton.setEnabled(false);
                minusButton.setEnabled(false);
                editButton.setEnabled(false);
            } else if (services != null) {
                plusButton.setEnabled(true);
                minusButton.setEnabled(true);
                editButton.setEnabled(true);
            }
        });

        final JPanel buttonsPanel = new JPanel(new FlowLayout(FlowLayout.CENTER));
        buttonsPanel.add(plusButton);
        buttonsPanel.add(editButton);
        buttonsPanel.add(minusButton);

        result.add(buttonsPanel, BorderLayout.SOUTH);
        return result;
    }

    private JComponent createLocsetsDeclarationsView() {
        final JPanel result = new JPanel(new BorderLayout());

        final JLabel titleLabel = new JLabel("Abstract Location Sets");
        final JPanel titleLabelContainer = new JPanel(new FlowLayout(FlowLayout.CENTER));
        titleLabelContainer.add(titleLabel);
        result.add(titleLabelContainer, BorderLayout.NORTH);

        final JList<AbstractLocsetDeclaration> locsetDeclsList = new JList<>();
        final JScrollPane scrollPane = new JScrollPane();
        scrollPane.setViewportView(locsetDeclsList);
        result.add(scrollPane, BorderLayout.CENTER);

        locsetDeclsList.setModel(locsetDeclsListModel);

        final JButton plusButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.PLUS, 16, Color.BLACK));
        plusButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                final AbstractLocsetDeclaration ls = LocsetInputDialog.showInputDialog( //
                        AERelationalDialog.this, services);
                if (ls != null) {
                    locsetDeclsListModel.addElement(ls);
                }
            }
        });

        final JButton editButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.PEN, 16, Color.BLACK));
        editButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                if (locsetDeclsList.getSelectedIndices().length == 1) {
                    final AbstractLocsetDeclaration selectedElem = //
                            locsetDeclsList.getSelectedValue();
                    final AbstractLocsetDeclaration ls = LocsetInputDialog.showInputDialog( //
                            AERelationalDialog.this, selectedElem, services);
                    if (ls != null) {
                        locsetDeclsListModel.set(locsetDeclsList.getSelectedIndex(), ls);
                    }
                }
            }
        });

        final JButton minusButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.MINUS, 16, Color.BLACK));
        minusButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                for (int idx : locsetDeclsList.getSelectedIndices()) {
                    locsetDeclsListModel.remove(idx);
                }
            }
        });

        plusButton.setEnabled(false);
        minusButton.setEnabled(false);
        editButton.setEnabled(false);

        this.servicesLoadedListeners.add(() -> {
            if (!isReadonly()) {
                plusButton.setEnabled(true);
                minusButton.setEnabled(true);
                editButton.setEnabled(true);
            }
        });
        this.readOnlyListeners.add(ro -> {
            if (ro) {
                plusButton.setEnabled(false);
                minusButton.setEnabled(false);
                editButton.setEnabled(false);
            } else if (services != null) {
                plusButton.setEnabled(true);
                minusButton.setEnabled(true);
                editButton.setEnabled(true);
            }
        });

        final JPanel buttonsPanel = new JPanel(new FlowLayout(FlowLayout.CENTER));
        buttonsPanel.add(plusButton);
        buttonsPanel.add(editButton);
        buttonsPanel.add(minusButton);

        result.add(buttonsPanel, BorderLayout.SOUTH);
        return result;
    }

    private JComponent createJavaEditorViewLeft() {
        return createJavaEditorView(codeLeft);
    }

    private JComponent createJavaEditorViewRight() {
        return createJavaEditorView(codeRight);
    }

    private JComponent createJavaEditorView(RSyntaxTextArea component) {
        component.setSyntaxEditingStyle(SyntaxConstants.SYNTAX_STYLE_JAVA);
        component.setCodeFoldingEnabled(true);

        final JavaErrorParser errorParser = new JavaErrorParser();

        programVariablesChangedListeners.add(errorParser::setProgVarDecls);
        readOnlyListeners.add(ro -> component.setEnabled(!ro));

        component.addParser(errorParser);
        return new RTextScrollPane(component);
    }

    public static List<Component> getAllComponents(final Container c) {
        Component[] comps = c.getComponents();
        List<Component> compList = new ArrayList<Component>();
        for (Component comp : comps) {
            compList.add(comp);
            if (comp instanceof Container)
                compList.addAll(getAllComponents((Container) comp));
        }
        return compList;
    }

    private static abstract class UniformListDataListener implements ListDataListener {

        @Override
        public void contentsChanged(ListDataEvent e) {
            listChanged(e);
        }

        @Override
        public void intervalAdded(ListDataEvent e) {
            listChanged(e);
        }

        @Override
        public void intervalRemoved(ListDataEvent e) {
            listChanged(e);
        }

        public abstract void listChanged(ListDataEvent e);
    }

    @FunctionalInterface
    private static interface ServicesLoadedListener {
        public void servicesLoaded();
    }

    @FunctionalInterface
    private static interface ReadonlyListener {
        public void readonlyChanged(boolean readonly);
    }

    @FunctionalInterface
    private static interface ProgramVariablesChangedListener {
        public void programVariablesChanged(Collection<ProgramVariableDeclaration> newVars);
    }
}
