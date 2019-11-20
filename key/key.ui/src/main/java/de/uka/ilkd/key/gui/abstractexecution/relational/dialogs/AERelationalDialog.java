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
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.regex.Pattern;

import javax.swing.AbstractAction;
import javax.swing.BorderFactory;
import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JRootPane;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.KeyStroke;
import javax.swing.SwingUtilities;
import javax.swing.event.DocumentEvent;
import javax.swing.event.ListDataEvent;
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
import de.uka.ilkd.key.gui.abstractexecution.relational.components.AutoResetStatusPanel;
import de.uka.ilkd.key.gui.abstractexecution.relational.components.FormulaInputTextArea;
import de.uka.ilkd.key.gui.abstractexecution.relational.components.JavaErrorParser;
import de.uka.ilkd.key.gui.abstractexecution.relational.listeners.DirtyListener;
import de.uka.ilkd.key.gui.abstractexecution.relational.listeners.ProgramVariablesChangedListener;
import de.uka.ilkd.key.gui.abstractexecution.relational.listeners.ReadonlyListener;
import de.uka.ilkd.key.gui.abstractexecution.relational.listeners.ServicesLoadedListener;
import de.uka.ilkd.key.gui.abstractexecution.relational.listeners.UniformDocumentListener;
import de.uka.ilkd.key.gui.abstractexecution.relational.listeners.UniformListDataListener;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.impl.ProverTaskAdapter;

/**
 * 
 * @author Dominic Steinhoefel
 */
public class AERelationalDialog extends JFrame {
    private static final String DUMMY_KEY_FILE = "/de/uka/ilkd/key/gui/abstractexecution/relational/dummy.key";
    private static final String PROOF_BUNDLE_ENDING = ".zproof";

    private static final String TITLE = "Relational Proofs with Abstract Execution";
    private static final int STATUS_PANEL_TIMEOUT = 2000;
    private static final int STATUS_PANEL_CHANGE_TIME = 30000;
    private static final String STATUS_PANEL_STD_MSG_1 = "Try to use tooltips if feeling unsure about the functionality of an element.";
    private static final String STATUS_PANEL_STD_MSG_2 = //
            "Recommended Example: File > Load Example > Abstract Execution > Consolidate Duplicate... > Extract Prefix";
    private static final String STATUS_PANEL_STD_MSG_3 = //
            "When declaring <tt>ae_constraint</tt>s, you have to put an empty block <tt>{ ; }</tt> after the JML comment.";

    private static final String STD_POSTCONDREL_TOOLTIP = "Relation between values of the relevant locations after execution.<br/>"
            + "You may use the keywords \"\\result_1\" and \"\\result_2\" to access<br/>"
            + "the respective result arrays.<br/>"
            + "Access individual values with \"\\result_1[2]\" etc. Use type casts<br/>"
            + "in non-trivial compound expressions.<br/>"
            + "At position [0], a returned value will be accessible.<br/>"
            + "At position [1], a potentially thrown Exception object will be<br/>"
            + "accessible which is null if no exception was thrown.<br/>";
    private static final String LOCSET_DECL_TOOLTIP = "<html>Abstract location sets for use in dynamic frames and footprints.<br/>"
            + "Syntax: E.g., 'nameForLocSet'.<br/>"
            + "Those locations can be used as 'relevant locations'.</html>";
    private static final String PROGVAR_DECL_TOOLTIP = "<html>Program variables available without declaration.<br/>"
            + "Syntax: E.g., 'int x', or 'java.lang.Object y'.<br/>"
            + "Those variables can be used as 'relevant locations'.</html>";
    private static final String PRED_DECL_TOOLTIP = "<html>Abstract predicates that can, e.g., be used to control<br/>"
            + "abrupt completion of abstract program elements.<br/>"
            + "Syntax: E.g., 'throwsExcP(any)'.<br/>"
            + "Can be used, e.g., in 'assumes' clauses in the abstract<br/>"
            + " program models.</html>";
    private static final String SAVE_BTN_TOOLTIP = "<html>Creates a KeY proof bundle at a temporary<br/>"
            + "location and starts the proof.</html>";
    private static final String TOOLTIP_REL_LOCS_RIGHT = "<html>Locations that are part of the result relation (for the<br/>"
            + "right program).<br/>"
            + "The i-th location in this list (i >= 1) is available via<br/>"
            + "\\result_2[i+1] in the 'Relation to Verify' text field.</html>";
    private static final String TOOLTIP_REL_LOCS_LEFT = "<html>Locations that are part of the result relation (for the<br/>"
            + "left program).<br/>"
            + "The i-th location in this list (i >= 1) is available via<br/>"
            + "\\result_1[i+1] in the 'Relation to Verify' text field.</html>";

    private static final long serialVersionUID = 1L;

    private AERelationalModel model;
    private MainWindow mainWindow;
    private Services services = null;
    // NOTE: Only access via setReadonly / isReadonly!
    private boolean readonly = false;
    // NOTE: Only access via setDirty / isDirty!
    private boolean dirty = false;

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
    private AutoResetStatusPanel statusPanel;

    private final List<ServicesLoadedListener> servicesLoadedListeners = new ArrayList<>();
    private final List<ProgramVariablesChangedListener> programVariablesChangedListeners = new ArrayList<>();
    private final List<ReadonlyListener> readOnlyListeners = new ArrayList<>();
    private final List<DirtyListener> dirtyListeners = new ArrayList<>();

    public static void main(String[] args) {
        final AERelationalModel model = AERelationalModel.EMPTY_MODEL;
        final AERelationalDialog dia = new AERelationalDialog(null, model);
        dia.setVisible(true);
    }

    public AERelationalDialog(MainWindow mainWindow, AERelationalModel model) {
        super(TITLE);

        assert model != null;
        this.model = model;
        this.mainWindow = mainWindow;

        setIconImage(IconFontSwing.buildImage(FontAwesomeSolid.BALANCE_SCALE, 16, Color.BLACK));
        setAlwaysOnTop(false);

        // We want to ask whether model should be saved
        setDefaultCloseOperation(DO_NOTHING_ON_CLOSE);

        final JPanel contentPanel = new JPanel(new BorderLayout());
        getContentPane().setLayout(new BorderLayout());
        getContentPane().add(contentPanel, BorderLayout.CENTER);
        statusPanel = new AutoResetStatusPanel( //
                STATUS_PANEL_TIMEOUT, STATUS_PANEL_CHANGE_TIME, STATUS_PANEL_STD_MSG_1,
                STATUS_PANEL_STD_MSG_2, STATUS_PANEL_STD_MSG_3);
        getContentPane().add(statusPanel, BorderLayout.SOUTH);

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

        statusPanel.setMessage("Initializing KeY data structures, please wait...");
        new Thread(() -> {
            initializeServices();
        }).start();

        /*
         * At the beginning, the model cannot be dirty. The flag will now be true,
         * though, since elements, in particular list models, have been populated with
         * initial content.
         */
        setDirty(false);
    }

    public void installListeners() {
        readOnlyListeners.add(ro -> {
            if (ro) {
                setTitle(String.format("%s (READ ONLY - Save to edit)", TITLE));
            } else {
                setTitle(TITLE);
            }
        });

        dirtyListeners.add(dirty -> {
            if (dirty) {
                setTitle(String.format("%s *", TITLE));
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
            statusPanel.setMessage("KeY data structures initialized successfully.");

            // Add special result symbols
            final Namespace<Function> functions = services.getNamespaces().functions();
            final Sort seqSort = services.getTypeConverter().getSeqLDT().targetSort();
            final Sort throwableSort = //
                    services.getJavaInfo().getKeYJavaType("java.lang.Throwable").getSort();

            functions.add(new Function(new Name(ProofBundleConverter.RES1), seqSort));
            functions.add(new Function(new Name(ProofBundleConverter.RES2), seqSort));
            functions.add(new Function(new Name(ProofBundleConverter.EXC), throwableSort));
        });

        addWindowListener(new WindowAdapter() {
            @Override
            public void windowClosing(WindowEvent e) {
                if (isDirty()) {
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
                } else {
                    setVisible(false);
                    dispose();
                }
            }
        });

        final KeyStroke controlS = KeyStroke.getKeyStroke(KeyEvent.VK_S, InputEvent.CTRL_MASK);
        final JRootPane rootPane = getRootPane();
        rootPane.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW).put(controlS, "saveModel");
        rootPane.getActionMap().put("saveModel", new AbstractAction() {
            private static final long serialVersionUID = 1L;

            @Override
            public void actionPerformed(ActionEvent e) {
                if (model.isSaved()) {
                    try {
                        if (!saveModelToFile(model.getFile().get())) {
                            statusPanel.setMessage(
                                    "ERROR: Problems saving model. Please save using the Save Model button.");
                        }
                    } catch (IOException exc) {
                        JOptionPane.showMessageDialog(AERelationalDialog.this,
                                "<html>Could not save model to file.<br><br/>Message:<br/>"
                                        + exc.getMessage() + "</html>",
                                "Problem Saving Model", JOptionPane.ERROR_MESSAGE);
                    } catch (JAXBException exc) {
                        JOptionPane.showMessageDialog(AERelationalDialog.this,
                                "<html>Could not save model ftorom file.<br><br/>Message:<br/>"
                                        + getMessageFromJAXBExc(exc) + "</html>",
                                "Problem Saving Model", JOptionPane.ERROR_MESSAGE);
                    }
                } else {
                    statusPanel.setMessage("Please save model first using the Save Model button.");
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

    public synchronized void setDirty(boolean dirty) {
        if (this.dirty != dirty) {
            this.dirty = dirty;
            dirtyListeners.forEach(l -> l.dirtyChanged(dirty));
        }
    }

    public boolean isDirty() {
        return dirty;
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
                                + e.getMessage(),
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
        model.getRelevantVarsTwo().forEach(relevantSymbolsTwoListModel::addElement);
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

    /**
     * First updates the model, then loads form the model. This is in particular
     * useful to react to changes in the {@link NullarySymbolDeclaration}s, because
     * this affects the relevant locations. When removing a
     * {@link NullarySymbolDeclaration}, potentially a relevant location has to be
     * removed, too.
     */
    private void refresh() {
        updateModel();
        loadFromModel();
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

        statusPanel.setMessage("Model successfully saved.");
        setDirty(false);

        return true;
    }

    private void loadFromFile() throws IOException, JAXBException, SAXException {
        if (isDirty()) {
            final int answer = JOptionPane.showConfirmDialog(AERelationalDialog.this,
                    "Do you want to save your model before loading another one?", "Save Model",
                    JOptionPane.YES_NO_OPTION, JOptionPane.QUESTION_MESSAGE);

            if (answer == JOptionPane.YES_OPTION) {
                try {
                    if (!saveModelToFile()) {
                        return;
                    }
                } catch (IOException | JAXBException exc) {
                    JOptionPane.showMessageDialog(AERelationalDialog.this,
                            "<html>Could not save model to file.<br><br/>Message:<br/>"
                                    + exc.getMessage() + "</html>",
                            "Problem Saving Model", JOptionPane.ERROR_MESSAGE);
                    return;
                }
            } else if (answer != JOptionPane.NO_OPTION) {
                return;
            }
        }

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
            setDirty(false);
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
            } catch (IOException exc) {
                JOptionPane.showMessageDialog(AERelationalDialog.this,
                        "<html>Could not load model from file.<br><br/>Message:<br/>"
                                + exc.getMessage() + "</html>",
                        "Problem Loading Model", JOptionPane.ERROR_MESSAGE);
            } catch (JAXBException exc) {
                JOptionPane.showMessageDialog(AERelationalDialog.this,
                        "<html>Could not load model from file.<br><br/>Message:<br/>"
                                + getMessageFromJAXBExc(exc) + "</html>",
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
            } catch (IOException exc) {
                JOptionPane.showMessageDialog(AERelationalDialog.this,
                        "<html>Could not save model to file.<br><br/>Message:<br/>"
                                + exc.getMessage() + "</html>",
                        "Problem Saving Model", JOptionPane.ERROR_MESSAGE);
            } catch (JAXBException exc) {
                JOptionPane.showMessageDialog(AERelationalDialog.this,
                        "<html>Could not save model ftorom file.<br><br/>Message:<br/>"
                                + getMessageFromJAXBExc(exc) + "</html>",
                        "Problem Saving Model", JOptionPane.ERROR_MESSAGE);
            }
        });

        final JButton saveBundleAndStartBtn = new JButton("Start Proof",
                IconFontSwing.buildIcon(FontAwesomeSolid.PLAY, 16, Color.BLACK));
        saveBundleAndStartBtn.setToolTipText(SAVE_BTN_TOOLTIP);
        saveBundleAndStartBtn.setPreferredSize(
                new Dimension(saveBundleAndStartBtn.getPreferredSize().width, 30));
        saveBundleAndStartBtn.addActionListener(e -> createAndLoadBundle());

        final JPanel ctrlPanel = new JPanel(new FlowLayout(FlowLayout.CENTER));
        ctrlPanel.add(loadFromFileBtn);
        ctrlPanel.add(saveToFileBtn);
        ctrlPanel.add(saveBundleAndStartBtn);

        return ctrlPanel;
    }

    private String getMessageFromJAXBExc(JAXBException exc) {
        return Optional.ofNullable(exc.getMessage())
                .orElse(Optional.ofNullable(exc.getLinkedException()).map(e -> e.getMessage())
                        .orElse(exc.toString()));
    }

    private void createAndLoadBundle() {
        updateModel();

        try {
            final String tmpFilePrefix = model.getFile().map(File::getName)
                    .orElse("AERelationalModel") + "_";
            final File proofBundleFile = Files.createTempFile( //
                    tmpFilePrefix, PROOF_BUNDLE_ENDING).toFile();
            final BundleSaveResult result = new ProofBundleConverter(model).save(proofBundleFile);

            final ProverTaskAdapter ptl = new ProverTaskAdapter() {
                @Override
                public void taskFinished(TaskFinishedInfo info) {
                    if (info == null) {
                        return;
                    }

                    if (info.getSource() instanceof ProblemLoader) {
                        if (info.getResult() == null
                                && !mainWindow.getMediator().getUI().isSaveOnly() && info.getProof()
                                        .getProofFile().getName().startsWith(tmpFilePrefix)) {
                            SwingUtilities.invokeLater(() -> mainWindow.getAutoModeAction().actionPerformed(null));
                            mainWindow.getUserInterface().removeProverTaskListener(this);
                            statusPanel.setMessage("Proof started.");
                        }
                    } else if (info.getSource() instanceof ProverCore) {
                        final Proof proof = info.getProof();
                        if (proof != null
                                && proof.getProofFile().getName().startsWith(tmpFilePrefix)) {
                            if (proof.closed()) {
                                statusPanel.setMessage("<b>Proof closed.</b>");
                            } else {
                                statusPanel.setMessage(
                                        String.format("Prover finished: <b>%d open goals</b>.",
                                                proof.openGoals().size()));
                            }
                        }
                    }
                }
            };
            mainWindow.getUserInterface().addProverTaskListener(ptl);
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

        final JComponent programOneView = createJavaEditorViewLeft();
        final JComponent programTwoView = createJavaEditorViewRight();

        final JSplitPane splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, true,
                programOneView, programTwoView);
        splitPane.setResizeWeight(.5);

        final JPanel editorsContainer = new JPanel(new BorderLayout());
        editorsContainer.setMinimumSize(new Dimension(600, 100));
        editorsContainer.add(splitPane, BorderLayout.CENTER);
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
        return createRelevantLocationsContainer("Relevant Locations (Left)", TOOLTIP_REL_LOCS_LEFT,
                relevantSymbolsOneListModel, AERelationalModel::getRelevantVarsOne);
    }

    private JPanel createRelevantLocationsTwoContainer() {
        return createRelevantLocationsContainer("Relevant Locations (Right)",
                TOOLTIP_REL_LOCS_RIGHT, relevantSymbolsTwoListModel,
                AERelationalModel::getRelevantVarsTwo);
    }

    private JPanel createRelevantLocationsContainer(String labelText, String toolTipText,
            DefaultListModel<NullarySymbolDeclaration> relevantSymbolsModel,
            java.util.function.Function<AERelationalModel, List<NullarySymbolDeclaration>> chosenRelevantSymbolsGetter) {
        relevantSymbolsModel.addListDataListener(new UniformListDataListener() {
            @Override
            public void listChanged(ListDataEvent e) {
                setDirty(true);
            }
        });

        final JPanel result = new JPanel(new BorderLayout());

        final JLabel titleLabel = new JLabel(labelText);
        final JPanel titleLabelContainer = new JPanel(new FlowLayout(FlowLayout.CENTER));
        titleLabelContainer.add(titleLabel);
        result.add(titleLabelContainer, BorderLayout.NORTH);

        final JList<NullarySymbolDeclaration> relevantSymbolsList = new JList<>();
        relevantSymbolsList.setToolTipText(toolTipText);
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
                            .showInputDialog(AERelationalDialog.this,
                                    "Please choose a relevant location to add",
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
        resultRelationText.setLineWrap(true);

        resultRelationText.getDocument().addDocumentListener(new UniformDocumentListener() {
            @Override
            public void documentChanged(DocumentEvent e) {
                setDirty(true);
            }
        });

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
        predDeclsList.setToolTipText(PRED_DECL_TOOLTIP);
        final JScrollPane scrollPane = new JScrollPane();
        scrollPane.setViewportView(predDeclsList);
        result.add(scrollPane, BorderLayout.CENTER);
        predDeclsList.setModel(predDeclsListModel);
        predDeclsListModel.addListDataListener(new UniformListDataListener() {
            @Override
            public void listChanged(ListDataEvent e) {
                setDirty(true);
            }
        });

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
                    services.getNamespaces().functions()
                            .remove(new Name(selectedElem.getPredName()));
                    final PredicateDeclaration pd = PredicateInputDialog
                            .showInputDialog(AERelationalDialog.this, selectedElem, services);
                    if (pd != null && !pd.equals(selectedElem)) {
                        predDeclsListModel.set(predDeclsList.getSelectedIndex(), pd);
                    } else {
                        try {
                            /* ...because names might be equal, but parameters changed. */
                            PredicateInputDialog.checkAndRegister(selectedElem, services);
                        } catch (ParserException exc) {
                        }
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
                    final PredicateDeclaration removed = predDeclsListModel.remove(idx);
                    services.getNamespaces().functions().remove(new Name(removed.getPredName()));
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

        final JList<ProgramVariableDeclaration> progVarDeclsList = new JList<>();
        progVarDeclsList.setToolTipText(PROGVAR_DECL_TOOLTIP);
        final JScrollPane scrollPane = new JScrollPane();
        scrollPane.setViewportView(progVarDeclsList);
        result.add(scrollPane, BorderLayout.CENTER);
        progVarDeclsList.setModel(progVarDeclsListModel);
        progVarDeclsListModel.addListDataListener(new UniformListDataListener() {
            @Override
            public void listChanged(ListDataEvent e) {
                programVariablesChangedListeners.forEach(l -> l.programVariablesChanged(
                        Collections.list(progVarDeclsListModel.elements())));
                setDirty(true);
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
                if (progVarDeclsList.getSelectedIndices().length == 1) {
                    final ProgramVariableDeclaration selectedElem = progVarDeclsList
                            .getSelectedValue();
                    final ProgramVariableDeclaration pd = ProgramVariableInputDialog
                            .showInputDialog(AERelationalDialog.this, selectedElem, services);
                    if (pd != null && !pd.equals(selectedElem)) {
                        services.getNamespaces().programVariables()
                                .remove(new Name(selectedElem.getName()));
                        progVarDeclsListModel.set(progVarDeclsList.getSelectedIndex(), pd);
                        refresh();
                    }
                }
            }
        });

        final JButton minusButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.MINUS, 16, Color.BLACK));
        minusButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                for (int idx : progVarDeclsList.getSelectedIndices()) {
                    final ProgramVariableDeclaration removed = progVarDeclsListModel.remove(idx);
                    services.getNamespaces().programVariables()
                            .remove(new Name(removed.getVarName()));
                    refresh();
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
        locsetDeclsList.setToolTipText(LOCSET_DECL_TOOLTIP);
        final JScrollPane scrollPane = new JScrollPane();
        scrollPane.setViewportView(locsetDeclsList);
        result.add(scrollPane, BorderLayout.CENTER);

        locsetDeclsList.setModel(locsetDeclsListModel);
        locsetDeclsListModel.addListDataListener(new UniformListDataListener() {
            @Override
            public void listChanged(ListDataEvent e) {
                setDirty(true);
            }
        });

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
                    if (ls != null && !ls.equals(selectedElem)) {
                        services.getNamespaces().functions()
                                .remove(new Name(selectedElem.getName()));
                        locsetDeclsListModel.set(locsetDeclsList.getSelectedIndex(), ls);
                        refresh();
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
                    final AbstractLocsetDeclaration removed = locsetDeclsListModel.remove(idx);
                    services.getNamespaces().functions().remove(new Name(removed.getName()));
                    refresh();
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
        component.getDocument().addDocumentListener(new UniformDocumentListener() {
            @Override
            public void documentChanged(DocumentEvent e) {
                setDirty(true);
            }
        });

        final JavaErrorParser errorParser = new JavaErrorParser();

        programVariablesChangedListeners.add(errorParser::setProgVarDecls);
        readOnlyListeners.add(ro -> component.setEnabled(!ro));

        component.addParser(errorParser);
        return new RTextScrollPane(component);
    }

    private static List<Component> getAllComponents(final Container c) {
        Component[] comps = c.getComponents();
        List<Component> compList = new ArrayList<Component>();
        for (Component comp : comps) {
            compList.add(comp);
            if (comp instanceof Container)
                compList.addAll(getAllComponents((Container) comp));
        }
        return compList;
    }
}
