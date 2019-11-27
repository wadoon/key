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

import static de.uka.ilkd.key.gui.abstractexecution.relational.listeners.UniformDocumentListener.udl;
import static de.uka.ilkd.key.gui.abstractexecution.relational.listeners.UniformListDataListener.uldl;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.Event;
import java.awt.FlowLayout;
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
import java.util.stream.Collectors;

import javax.swing.AbstractAction;
import javax.swing.BorderFactory;
import javax.swing.DefaultListModel;
import javax.swing.InputMap;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JRootPane;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JToolBar;
import javax.swing.KeyStroke;
import javax.swing.SwingUtilities;
import javax.xml.bind.JAXBException;

import org.fife.ui.rsyntaxtextarea.CodeTemplateManager;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.SyntaxConstants;
import org.fife.ui.rsyntaxtextarea.Theme;
import org.fife.ui.rsyntaxtextarea.templates.StaticCodeTemplate;
import org.fife.ui.rtextarea.RTextScrollPane;
import org.xml.sax.SAXException;

import bibliothek.gui.dock.common.CContentArea;
import bibliothek.gui.dock.common.CControl;
import bibliothek.gui.dock.common.CGrid;
import bibliothek.gui.dock.common.DefaultSingleCDockable;
import de.uka.ilkd.key.abstractexecution.relational.model.AERelationalModel;
import de.uka.ilkd.key.abstractexecution.relational.model.AbstractLocsetDeclaration;
import de.uka.ilkd.key.abstractexecution.relational.model.FuncOrPredDecl;
import de.uka.ilkd.key.abstractexecution.relational.model.FunctionDeclaration;
import de.uka.ilkd.key.abstractexecution.relational.model.NullarySymbolDeclaration;
import de.uka.ilkd.key.abstractexecution.relational.model.PredicateDeclaration;
import de.uka.ilkd.key.abstractexecution.relational.model.ProgramVariableDeclaration;
import de.uka.ilkd.key.abstractexecution.relational.model.ProofBundleConverter;
import de.uka.ilkd.key.abstractexecution.relational.model.ProofBundleConverter.BundleSaveResult;
import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.abstractexecution.relational.components.AutoResetStatusPanel;
import de.uka.ilkd.key.gui.abstractexecution.relational.components.FormulaInputTextArea;
import de.uka.ilkd.key.gui.abstractexecution.relational.components.JavaErrorParser;
import de.uka.ilkd.key.gui.abstractexecution.relational.components.MethodLevelJavaErrorParser;
import de.uka.ilkd.key.gui.abstractexecution.relational.components.StatementLevelJavaErrorParser;
import de.uka.ilkd.key.gui.abstractexecution.relational.listeners.DirtyListener;
import de.uka.ilkd.key.gui.abstractexecution.relational.listeners.MethodContextChangedListener;
import de.uka.ilkd.key.gui.abstractexecution.relational.listeners.ProgramVariablesChangedListener;
import de.uka.ilkd.key.gui.abstractexecution.relational.listeners.ReadonlyListener;
import de.uka.ilkd.key.gui.abstractexecution.relational.listeners.ResetUndosListener;
import de.uka.ilkd.key.gui.abstractexecution.relational.listeners.ServicesLoadedListener;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
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
public class AERelationalDialog extends JFrame implements AERelationalDialogConstants {
    private static final long serialVersionUID = 1L;

    private AERelationalModel model;
    private MainWindow mainWindow;
    private Services services = null;
    // NOTE: Only access via setReadonly / isReadonly!
    private boolean readonly = false;
    // NOTE: Only access via setDirty / isDirty!
    private boolean dirty = false;

    private final DefaultListModel<AbstractLocsetDeclaration> locsetDeclsListModel = new DefaultListModel<>();
    private final DefaultListModel<FuncOrPredDecl> funcOrPredDeclsListModel = new DefaultListModel<>();
    private final DefaultListModel<ProgramVariableDeclaration> progVarDeclsListModel = new DefaultListModel<>();
    private final DefaultListModel<NullarySymbolDeclaration> relevantSymbolsOneListModel = new DefaultListModel<>();
    private final DefaultListModel<NullarySymbolDeclaration> relevantSymbolsTwoListModel = new DefaultListModel<>();

    private final RSyntaxTextArea codeLeft = new RSyntaxTextArea(15, 60);
    private final RSyntaxTextArea codeRight = new RSyntaxTextArea(15, 60);
    private final RSyntaxTextArea codeContext = new RSyntaxTextArea(15, 120);

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
    private final List<MethodContextChangedListener> methodContextChangedListeners = new ArrayList<>();
    private final List<ReadonlyListener> readOnlyListeners = new ArrayList<>();
    private final List<DirtyListener> dirtyListeners = new ArrayList<>();
    private final List<ResetUndosListener> resetUndosListeners = new ArrayList<>();

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

        installCodeTemplates();

        final JPanel contentPanel = createContentPanel();

        getContentPane().setLayout(new BorderLayout());
        getContentPane().add(contentPanel, BorderLayout.CENTER);
        getAllComponents(contentPanel).stream().filter(JButton.class::isInstance)
                .map(JButton.class::cast).forEach(btn -> btn.setBackground(Color.WHITE));

        setPreferredSize(new Dimension(1400, 800));
        pack();

        loadFromModel();
        installListeners();

        statusPanel.setMessage("Initializing KeY data structures, please wait...");
        new Thread(() -> initializeServices()).start();

        /*
         * At the beginning, the model cannot be dirty. The flag will now be true,
         * though, since elements, in particular list models, have been populated with
         * initial content.
         */
        setDirty(false);
        updateTitle();
        resetUndosListeners.forEach(ResetUndosListener::resetUndos);
    }

    private JPanel createContentPanel() {
        final JPanel contentPanel = new JPanel(new BorderLayout());
        statusPanel = new AutoResetStatusPanel( //
                STATUS_PANEL_TIMEOUT, STATUS_PANEL_CHANGE_TIME, STATUS_PANEL_STD_MSG_1,
                STATUS_PANEL_STD_MSG_2, STATUS_PANEL_STD_MSG_3, STATUS_PANEL_STD_MSG_4);

        contentPanel.add(createControlToolbar(), BorderLayout.NORTH);
        contentPanel.add(createDockingSetup(), BorderLayout.CENTER);
        contentPanel.add(statusPanel, BorderLayout.SOUTH);
        
        return contentPanel;
    }

    private CContentArea createDockingSetup() {
        final CControl control = new CControl(this);

        final JComponent programVariableDeclarations = createProgramVariableDeclarationsView();
        final JComponent locsetsDeclarations = createLocsetsDeclarationsView();
        final JComponent formulaDeclarations = createPredicatesDeclarationsView();

        final JComponent programFragmentsComt = createAbstractFragmentViewContainer();
        final JComponent methodContextComt = createMethodLevelContextViewContainer();

        final JPanel relLocsLeft = createRelevantLocationsOneContainer();
        final JPanel relLocsRight = createRelevantLocationsTwoContainer();
        final JPanel postRelation = createResultRelationView();

        final DefaultSingleCDockable pvDockable = new DefaultSingleCDockable(
                "Free Program Variables", "Free Program Variables", programVariableDeclarations);
        final DefaultSingleCDockable locsetDockable = new DefaultSingleCDockable(
                "Abstract Location Sets", "Abstract Location Sets", locsetsDeclarations);
        final DefaultSingleCDockable formulaDockable = new DefaultSingleCDockable(
                "Functions and Predicates", "Functions and Predicates", formulaDeclarations);
        final DefaultSingleCDockable progFragmDockable = new DefaultSingleCDockable(
                "Abstract Program Fragments", "Abstract Program Fragments", programFragmentsComt);
        final DefaultSingleCDockable methodContextDockable = new DefaultSingleCDockable(
                "Method-Level Context", "Method-Level Context", methodContextComt);
        final DefaultSingleCDockable relLocsLeftDockable = new DefaultSingleCDockable(
                "Relevant Locations (Left)", "Relevant Locations (Left)", relLocsLeft);
        final DefaultSingleCDockable relLocsRightDockable = new DefaultSingleCDockable(
                "Relevant Locations (Right)", "Relevant Locations (Right)", relLocsRight);
        final DefaultSingleCDockable relationDockable = new DefaultSingleCDockable(
                "Relation to Verify", "Relation to Verify", postRelation);

        final CGrid grid = new CGrid(control);

        grid.add(0, 0, 1, 3, pvDockable);
        grid.add(0, 3, 1, 3, locsetDockable);
        grid.add(0, 6, 1, 3, formulaDockable);

        grid.add(1, 7, 1, 2, relLocsLeftDockable);
        grid.add(2, 7, 1, 2, relLocsRightDockable);
        grid.add(3, 7, 2, 2, relationDockable);

        grid.add(1, 0, 4, 7, methodContextDockable);
        grid.add(1, 0, 4, 7, progFragmDockable);

        final CContentArea dockingContentArea = control.getContentArea();
        dockingContentArea.deploy(grid);
        return dockingContentArea;
    }

    private static void installCodeTemplates() {
        /*
         * Whether templates are enabled is a global property affecting all
         * RSyntaxTextAreas, so this method is static.
         */
        RSyntaxTextArea.setTemplatesEnabled(true);

        final CodeTemplateManager ctm = RSyntaxTextArea.getCodeTemplateManager();

        for (String[] codeTemplate : CODE_TEMPLATES) {
            ctm.addTemplate(new StaticCodeTemplate(codeTemplate[0], codeTemplate[1], null));
        }
    }

    private void updateTitle() {
        setTitle(String.format("%s [%s%s]%s", TITLE,
                model.getFile().map(File::getName).orElse("No File"),
                isDirty() ? AERelationalDialogConstants.DIRTY_TITLE_PART : "",
                isReadonly() ? AERelationalDialogConstants.READ_ONLY_TITLE_PART : ""));
    }

    public void installListeners() {
        readOnlyListeners.add(ro -> {
            updateTitle();
        });

        dirtyListeners.add(dirty -> {
            updateTitle();
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
                    FuncAndPredInputDialog.checkAndRegister(pred, services);
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
        codeContext.setText(model.getMethodLevelContext());
        resultRelationText.setText(model.getPostCondition());

        locsetDeclsListModel.clear();
        model.getAbstractLocationSets().forEach(locsetDeclsListModel::addElement);
        funcOrPredDeclsListModel.clear();
        model.getFunctionDeclarations().forEach(funcOrPredDeclsListModel::addElement);
        model.getPredicateDeclarations().forEach(funcOrPredDeclsListModel::addElement);
        progVarDeclsListModel.clear();
        model.getProgramVariableDeclarations().forEach(progVarDeclsListModel::addElement);
        relevantSymbolsOneListModel.clear();
        model.getRelevantVarsOne().forEach(relevantSymbolsOneListModel::addElement);
        relevantSymbolsTwoListModel.clear();
        model.getRelevantVarsTwo().forEach(relevantSymbolsTwoListModel::addElement);

        methodContextChangedListeners
                .forEach(l -> l.methodContextChanged(model.getMethodLevelContext()));
    }

    private void updateModel() {
        model.setProgramOne(codeLeft.getText());
        model.setProgramTwo(codeRight.getText());
        model.setMethodLevelContext(codeContext.getText());
        model.setPostCondition(resultRelationText.getText());
        model.setAbstractLocationSets(Collections.list(locsetDeclsListModel.elements()));
        model.setFunctionDeclarations(Collections.list(funcOrPredDeclsListModel.elements()).stream()
                .filter(FunctionDeclaration.class::isInstance).map(FunctionDeclaration.class::cast)
                .collect(Collectors.toList()));
        model.setPredicateDeclarations(Collections.list(funcOrPredDeclsListModel.elements())
                .stream().filter(PredicateDeclaration.class::isInstance)
                .map(PredicateDeclaration.class::cast).collect(Collectors.toList()));
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
        updateTitle();

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

            final AERelationalModel newModel = AERelationalModel
                    .fromXml(new String(Files.readAllBytes(file.toPath())));
            newModel.setFile(file);

            if (isDirty()) {
                final AERelationalDialog newDia = new AERelationalDialog(mainWindow, newModel);
                newDia.setVisible(true);
            } else {
                model = newModel;
                model.setFile(file);
                updateTitle();
                loadFromModel();
                setDirty(false);
                resetUndosListeners.forEach(ResetUndosListener::resetUndos);
            }
        }
    }

    private JToolBar createControlToolbar() {
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

        /*
         * MainWindow might not be there when testing the dialog with local main
         * function
         */
        final Optional<MainWindow> maybeMainWindow = Optional.ofNullable(mainWindow);
        maybeMainWindow.ifPresent(m -> m.getUserInterface().getProofControl()
                .addAutoModeListener(new AutoModeListener() {
                    @Override
                    public void autoModeStarted(ProofEvent e) {
                        SwingUtilities.invokeLater(() -> saveBundleAndStartBtn.setEnabled(false));
                    }

                    @Override
                    public void autoModeStopped(ProofEvent e) {
                        try {
                            Thread.sleep(1500);
                        } catch (InterruptedException exc) {
                        }
                        SwingUtilities.invokeLater(() -> saveBundleAndStartBtn.setEnabled(true));
                    }
                }));

        final JToolBar toolBar = new JToolBar();
        toolBar.setBorder(BorderFactory.createCompoundBorder(toolBar.getBorder(),
                BorderFactory.createEmptyBorder(4, 0, 2, 0)));

        toolBar.setFloatable(true);
        toolBar.setRollover(true);

        toolBar.add(loadFromFileBtn);
        toolBar.addSeparator();
        toolBar.add(saveToFileBtn);
        toolBar.addSeparator();
        toolBar.addSeparator();
        toolBar.add(saveBundleAndStartBtn);

        return toolBar;
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
                            SwingUtilities.invokeLater(
                                    () -> mainWindow.getAutoModeAction().actionPerformed(null));
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
            SwingUtilities.invokeLater(() -> mainWindow.loadProofFromBundle(result.getFile(),
                    result.getProofPath().toFile()));

        } catch (IOException | IllegalStateException e) {
            JOptionPane
                    .showMessageDialog(AERelationalDialog.this,
                            "<html>Problem saving proof bundle.<br/><br/>Message:<br/>"
                                    + e.getMessage() + "</html>",
                            "Problem Starting Proof", JOptionPane.ERROR_MESSAGE);
        }
    }

    private JComponent createAbstractFragmentViewContainer() {
        final StatementLevelJavaErrorParser stmtLevelErrorParser = new StatementLevelJavaErrorParser();
        programVariablesChangedListeners.add(stmtLevelErrorParser::setProgVarDecls);
        methodContextChangedListeners.add(stmtLevelErrorParser::setMethodLevelContext);

        final JSplitPane splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, true,
                createJavaEditorView(codeLeft, stmtLevelErrorParser),
                createJavaEditorView(codeRight, stmtLevelErrorParser));
        splitPane.setResizeWeight(.5);

        return splitPane;
    }

    private JComponent createMethodLevelContextViewContainer() {
        codeContext.getDocument().addDocumentListener(udl(e -> methodContextChangedListeners
                .forEach(l -> l.methodContextChanged(e.getDocument().toString()))));
        return createJavaEditorView(codeContext, new MethodLevelJavaErrorParser());
    }

    private JPanel createRelevantLocationsOneContainer() {
        return createRelevantLocationsContainer(TOOLTIP_REL_LOCS_LEFT, relevantSymbolsOneListModel,
                AERelationalModel::getRelevantVarsOne);
    }

    private JPanel createRelevantLocationsTwoContainer() {
        return createRelevantLocationsContainer(TOOLTIP_REL_LOCS_RIGHT, relevantSymbolsTwoListModel,
                AERelationalModel::getRelevantVarsTwo);
    }

    private JPanel createRelevantLocationsContainer(String toolTipText,
            DefaultListModel<NullarySymbolDeclaration> relevantSymbolsModel,
            java.util.function.Function<AERelationalModel, List<NullarySymbolDeclaration>> chosenRelevantSymbolsGetter) {
        relevantSymbolsModel.addListDataListener(uldl(e -> setDirty(true)));

        final JPanel result = new JPanel(new BorderLayout());

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
                final int[] indices = relevantSymbolsList.getSelectedIndices();
                for (int i = indices.length; i-- > 0;) {
                    int idx = indices[i];
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

    private JPanel createResultRelationView() {
        final JPanel postCondContainer = new JPanel(new BorderLayout());

        resultRelationText.setBorder(BorderFactory.createEtchedBorder());
        resultRelationText.setEnabled(false);
        resultRelationText.setBorder(BorderFactory.createCompoundBorder(
                resultRelationText.getBorder(), BorderFactory.createEmptyBorder(5, 5, 5, 5)));
        resultRelationText.setLineWrap(true);

        resultRelationText.getDocument().addDocumentListener(udl(e -> setDirty(true)));

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

        final JList<FuncOrPredDecl> predDeclsList = new JList<>();
        predDeclsList.setToolTipText(FUNC_OR_PRED_DECL_TOOLTIP);
        final JScrollPane scrollPane = new JScrollPane();
        scrollPane.setViewportView(predDeclsList);
        result.add(scrollPane, BorderLayout.CENTER);
        predDeclsList.setModel(funcOrPredDeclsListModel);
        funcOrPredDeclsListModel.addListDataListener(uldl(e -> setDirty(true)));

        final JButton plusButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.PLUS, 16, Color.BLACK));
        plusButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                final FuncOrPredDecl pd = FuncAndPredInputDialog
                        .showInputDialog(AERelationalDialog.this, services);
                if (pd != null) {
                    funcOrPredDeclsListModel.addElement(pd);
                }
            }
        });

        final JButton editButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.PEN, 16, Color.BLACK));
        editButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                if (predDeclsList.getSelectedIndices().length == 1) {
                    final FuncOrPredDecl selectedElem = predDeclsList.getSelectedValue();
                    services.getNamespaces().functions().remove(new Name(selectedElem.getName()));
                    final FuncOrPredDecl pd = FuncAndPredInputDialog
                            .showInputDialog(AERelationalDialog.this, selectedElem, services);
                    if (pd != null && !pd.equals(selectedElem)) {
                        funcOrPredDeclsListModel.set(predDeclsList.getSelectedIndex(), pd);
                    } else {
                        try {
                            /* ...because names might be equal, but parameters changed. */
                            FuncAndPredInputDialog.checkAndRegister(selectedElem, services);
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
                final int[] indices = predDeclsList.getSelectedIndices();
                for (int i = indices.length; i-- > 0;) {
                    int idx = indices[i];
                    final FuncOrPredDecl removed = funcOrPredDeclsListModel.remove(idx);
                    services.getNamespaces().functions().remove(new Name(removed.getName()));
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

        final JList<ProgramVariableDeclaration> progVarDeclsList = new JList<>();
        progVarDeclsList.setToolTipText(PROGVAR_DECL_TOOLTIP);
        final JScrollPane scrollPane = new JScrollPane();
        scrollPane.setViewportView(progVarDeclsList);
        result.add(scrollPane, BorderLayout.CENTER);
        progVarDeclsList.setModel(progVarDeclsListModel);
        progVarDeclsListModel.addListDataListener(uldl(e -> {
            setDirty(true);
            programVariablesChangedListeners.forEach(l -> l.programVariablesChanged( //
                    Collections.list(progVarDeclsListModel.elements())));
        }));

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
                final int[] indices = progVarDeclsList.getSelectedIndices();
                for (int i = indices.length; i-- > 0;) {
                    int idx = indices[i];
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

        final JList<AbstractLocsetDeclaration> locsetDeclsList = new JList<>();
        locsetDeclsList.setToolTipText(LOCSET_DECL_TOOLTIP);
        final JScrollPane scrollPane = new JScrollPane();
        scrollPane.setViewportView(locsetDeclsList);
        result.add(scrollPane, BorderLayout.CENTER);

        locsetDeclsList.setModel(locsetDeclsListModel);
        locsetDeclsListModel.addListDataListener(uldl(e -> setDirty(true)));

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
                final int[] indices = locsetDeclsList.getSelectedIndices();
                for (int i = indices.length; i-- > 0;) {
                    int idx = indices[i];
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

    private JComponent createJavaEditorView(RSyntaxTextArea component,
            JavaErrorParser errorParser) {
        resetUndosListeners.add(() -> component.discardAllEdits());

        component.addParser(errorParser);
        component.setSyntaxEditingStyle(SyntaxConstants.SYNTAX_STYLE_JAVA);
        component.setCodeFoldingEnabled(true);
        component.setTabSize(4);
        component.setTabsEmulated(true);

        // Set eclipse theme
        try {
            final Theme theme = Theme.load(
                    getClass().getResourceAsStream("/org/fife/ui/rsyntaxtextarea/themes/idea.xml"));
            theme.apply(component);
        } catch (IOException ioe) {
            // Shouldn't happen; never mind if it does.
        }

        component.getDocument().addDocumentListener(udl(e -> setDirty(true)));

        final InputMap inputMap = component.getInputMap();

        final KeyStroke undoKey = KeyStroke.getKeyStroke(KeyEvent.VK_Z, Event.CTRL_MASK);
        inputMap.put(undoKey, new AbstractAction() {
            private static final long serialVersionUID = 1L;

            @Override
            public void actionPerformed(ActionEvent e) {
                if (component.canUndo()) {
                    component.undoLastAction();
                }
            }
        });

        final KeyStroke redoKey = KeyStroke.getKeyStroke(KeyEvent.VK_Y, Event.CTRL_MASK);
        inputMap.put(redoKey, new AbstractAction() {
            private static final long serialVersionUID = 1L;

            @Override
            public void actionPerformed(ActionEvent e) {
                if (component.canRedo()) {
                    component.redoLastAction();
                }
            }
        });

        readOnlyListeners.add(ro -> component.setEnabled(!ro));

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
