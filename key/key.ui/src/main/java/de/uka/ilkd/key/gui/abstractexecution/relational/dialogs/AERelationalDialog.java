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
import java.io.BufferedInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

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
import org.key_project.util.helper.FindResources;
import org.xml.sax.SAXException;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.abstractexecution.relational.components.FormulaInputTextField;
import de.uka.ilkd.key.gui.abstractexecution.relational.model.AERelationalModel;
import de.uka.ilkd.key.gui.abstractexecution.relational.model.PredicateDeclaration;
import de.uka.ilkd.key.gui.abstractexecution.relational.model.ProgramVariableDeclaration;
import de.uka.ilkd.key.gui.abstractexecution.relational.model.ProofBundleConverter;
import de.uka.ilkd.key.gui.abstractexecution.relational.model.ProofBundleConverter.BundleSaveResult;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * 
 * @author Dominic Steinhoefel
 */
public class AERelationalDialog extends JDialog {
    private static final String JAVA_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/gui/abstractexecution/relational/Problem.java";
    private static final String KEY_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/gui/abstractexecution/relational/problem.key";
    private static final String DUMMY_KEY_FILE = "/de/uka/ilkd/key/gui/abstractexecution/relational/dummy.key";

    private static final long serialVersionUID = 1L;

    private AERelationalModel model;
    private MainWindow mainWindow;
    private Services services = null;

    private final DefaultListModel<String> locsetDeclsListModel = new DefaultListModel<>();
    private final DefaultListModel<PredicateDeclaration> predDeclsListModel = new DefaultListModel<>();
    private final DefaultListModel<ProgramVariableDeclaration> progVarDeclsListModel = new DefaultListModel<>();
    private final RSyntaxTextArea codeLeft = new RSyntaxTextArea(20, 60);
    private final RSyntaxTextArea codeRight = new RSyntaxTextArea(20, 60);
    private final FormulaInputTextField postCondTextField = new FormulaInputTextField();

    private final List<ServicesLoadedListener> servicesLoadedListeners = new ArrayList<>();
    private final List<ProgramVariablesChangedListener> programVariablesChangedListeners = new ArrayList<>();

    public AERelationalDialog(MainWindow mainWindow, AERelationalModel model) {
        super(mainWindow, false);

        assert model != null;
        this.model = model;
        this.mainWindow = mainWindow;

        setTitle("Relational Proofs with Abstract Execution");
        setIconImage(IconFontSwing.buildImage(FontAwesomeSolid.BALANCE_SCALE, 16, Color.BLACK));
        setDefaultCloseOperation(DISPOSE_ON_CLOSE);

        final JPanel contentPanel = new JPanel(new BorderLayout());
        getContentPane().setLayout(new BorderLayout());
        getContentPane().add(contentPanel, BorderLayout.CENTER);

        final JPanel declarationsContainer = createDeclarationsContainer();
        final JPanel programViewContainer = createProgramViewContainer();

        final JSplitPane splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
                declarationsContainer, programViewContainer);
        splitPane.setOneTouchExpandable(true);
        contentPanel.add(splitPane, BorderLayout.CENTER);

        final JPanel ctrlPanel = createControlPanel();
        contentPanel.add(ctrlPanel, BorderLayout.SOUTH);

        getAllComponents(contentPanel).stream().filter(JButton.class::isInstance)
                .map(JButton.class::cast).forEach(btn -> btn.setBackground(Color.WHITE));

        final int preferredWidth = programViewContainer.getPreferredSize().width
                + declarationsContainer.getPreferredSize().width + 10;

        postCondTextField.setEnabled(false);
        servicesLoadedListeners.add(() -> {
            postCondTextField.setServices(services);
            postCondTextField.setEnabled(true);
        });

        setPreferredSize(new Dimension(preferredWidth, 700));
        pack();

        loadFromModel();
        new Thread(() -> {
            initializeServices();
        }).start();

        servicesLoadedListeners.add(() -> {
            final NamespaceSet namespaces = services.getNamespaces();

            model.getAbstractLocationSets().forEach(loc -> {
                namespaces.functions().add(new Function(new Name(loc),
                        services.getTypeConverter().getLocSetLDT().targetSort()));
            });

            model.getProgramVariableDeclarations().forEach(loc -> {
                MergeRuleUtils.parsePlaceholder(loc.getTypeName() + " " + loc.getVarName(),
                        services);
            });

            model.getPredicateDeclarations().forEach(val -> {
                final List<Sort> sorts = //
                        val.getArgSorts().stream().map(namespaces.sorts()::lookup)
                                .collect(Collectors.toList());
                final Function function = new Function( //
                        new Name(val.getPredName()), Sort.FORMULA, sorts.toArray(new Sort[0]));
                namespaces.functions().add(function);
            });
        });
    }

    private void initializeServices() {
        final URL keyFileUrl = AERelationalDialog.class.getResource(DUMMY_KEY_FILE);

        if (keyFileUrl == null) {
            SwingUtilities.invokeLater(() -> {
                JOptionPane.showMessageDialog(AERelationalDialog.this,
                        "Ooops... Could not load resource file!", "Problem During Initialization",
                        JOptionPane.ERROR_MESSAGE);
            });
            return;
        }

        KeYEnvironment<?> environment = null;
        try {
            final File keyFile = //
                    FindResources.getResource(DUMMY_KEY_FILE, AERelationalDialog.class).toFile();
            environment = KeYEnvironment.load( //
                    JavaProfile.getDefaultInstance(), keyFile, null, null, null, true);
        } catch (ProblemLoaderException | URISyntaxException | IOException e) {
            SwingUtilities.invokeLater(() -> {
                JOptionPane.showMessageDialog(AERelationalDialog.this,
                        "Ooops... Could not initialize proof services!",
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
        postCondTextField.setText(model.getPostCondition());

        locsetDeclsListModel.clear();
        model.getAbstractLocationSets().forEach(locsetDeclsListModel::addElement);
        predDeclsListModel.clear();
        model.getPredicateDeclarations().forEach(predDeclsListModel::addElement);
        progVarDeclsListModel.clear();
        model.getProgramVariableDeclarations().forEach(progVarDeclsListModel::addElement);
    }

    private void updateModel() {
        model.setProgramOne(codeLeft.getText());
        model.setProgramTwo(codeRight.getText());
        model.setPostCondition(postCondTextField.getText());
        model.setAbstractLocationSets(Collections.list(locsetDeclsListModel.elements()));
        model.setPredicateDeclarations(Collections.list(predDeclsListModel.elements()));
        model.setProgramVariableDeclarations(Collections.list(progVarDeclsListModel.elements()));
    }

    private void saveModelToFile() throws IOException, JAXBException {
        final KeYFileChooser chooser = KeYFileChooser
                .getFileChooser("Choose Destination for AE-Relational Model");

        final boolean saveResult = model.getFile()
                .map(f -> chooser.showSaveDialog(AERelationalDialog.this, f))
                .orElseGet(() -> chooser.showSaveDialog(AERelationalDialog.this, null, ".aer"));
        if (saveResult) {
            saveModelToFile(chooser.getSelectedFile());
        }
    }

    private void saveModelToFile(File file) throws IOException, JAXBException {
        updateModel();
        Files.write(file.toPath(), model.toXml().getBytes());
        model.setFile(file);
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

    private static String inputStreamToString(InputStream is) throws IOException {
        final StringBuilder sb = new StringBuilder();
        final BufferedInputStream in = new BufferedInputStream(is);
        byte[] contents = new byte[1024];

        int bytesRead = 0;
        while ((bytesRead = in.read(contents)) != -1) {
            sb.append(new String(contents, 0, bytesRead));
        }

        return sb.toString();
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

        final JButton saveBundleAndStartBtn = new JButton("Bundle & Start",
                IconFontSwing.buildIcon(FontAwesomeSolid.PLAY, 16, Color.BLACK));
        saveBundleAndStartBtn.setPreferredSize(
                new Dimension(saveBundleAndStartBtn.getPreferredSize().width, 30));
        saveBundleAndStartBtn.addActionListener(e -> saveAndStartBundle());

        final JPanel ctrlPanel = new JPanel(new FlowLayout(FlowLayout.CENTER));
        ctrlPanel.add(loadFromFileBtn);
        ctrlPanel.add(saveToFileBtn);
        ctrlPanel.add(saveBundleAndStartBtn);

        return ctrlPanel;
    }

    private void saveAndStartBundle() {
        if (!model.isSaved()) {
            JOptionPane.showMessageDialog(AERelationalDialog.this, "Please first save the model.",
                    "Problem Starting Proof", JOptionPane.ERROR_MESSAGE);
            return;
        }

        try {
            saveModelToFile(model.getFile().get());
        } catch (IOException | JAXBException exc) {
            JOptionPane
                    .showMessageDialog(AERelationalDialog.this,
                            "<html>Could not save model to file.<br><br/>Message:<br/>"
                                    + exc.getMessage() + "</html>",
                            "Problem Starting Proof", JOptionPane.ERROR_MESSAGE);
            return;
        }

        final InputStream javaScaffoldIS = AERelationalDialog.class
                .getResourceAsStream(JAVA_PROBLEM_FILE_SCAFFOLD);
        final InputStream keyScaffoldIS = AERelationalDialog.class
                .getResourceAsStream(KEY_PROBLEM_FILE_SCAFFOLD);
        if (javaScaffoldIS == null || keyScaffoldIS == null) {
            JOptionPane.showMessageDialog(AERelationalDialog.this,
                    "Ooops... Could not load resource file!", "Problem Starting Proof",
                    JOptionPane.ERROR_MESSAGE);
            return;
        }

        String javaScaffold = null;
        String keyScaffold = null;
        try {
            javaScaffold = inputStreamToString(javaScaffoldIS);
            keyScaffold = inputStreamToString(keyScaffoldIS);
        } catch (IOException e) {
            JOptionPane.showMessageDialog(AERelationalDialog.this,
                    "Ooops... Could not load resource file!", "Problem Starting Proof",
                    JOptionPane.ERROR_MESSAGE);
        }

        try {
            final ProofBundleConverter pbc = //
                    new ProofBundleConverter(model, javaScaffold, keyScaffold);
            final BundleSaveResult result = pbc.save(model.getFile()
                    .map(f -> new File(f.getParent(), f.getName().replaceAll(".aer", ".zproof")))
                    .get());
            mainWindow.loadProofFromBundle(result.getFile(), result.getProofPath().toFile());
        } catch (IOException e) {
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
        final JPanel programViewContainer = new JPanel(new GridLayout(1, 2));
        programViewContainer.add(programOneView);
        programViewContainer.add(programTwoView);
        programViewContainer.setMinimumSize(new Dimension(600, 100));
        return programViewContainer;
    }

    private JPanel createDeclarationsContainer() {
        final JPanel symbolDeclContainer = new JPanel(new GridLayout(3, 1));

        final JComponent programVariableDeclarations = createProgramVariableDeclarationsView();
        final JComponent locsetsDeclarations = createLocsetsDeclarationsView();
        final JComponent formulaDeclarations = createPredicatesDeclarationsView();

        programVariableDeclarations.setBorder(BorderFactory.createEmptyBorder(0, 0, 5, 0));
        locsetsDeclarations.setBorder(BorderFactory.createEmptyBorder(5, 0, 5, 0));
        formulaDeclarations.setBorder(BorderFactory.createEmptyBorder(5, 0, 5, 0));

        symbolDeclContainer.add(programVariableDeclarations);
        symbolDeclContainer.add(locsetsDeclarations);
        symbolDeclContainer.add(formulaDeclarations);

        final JPanel postCond = createPostConditionView();
        postCond.setBorder(BorderFactory.createEmptyBorder(5, 0, 0, 0));

        final JPanel declContainer = new JPanel(new BorderLayout());
        declContainer.add(symbolDeclContainer, BorderLayout.CENTER);
        declContainer.add(postCond, BorderLayout.SOUTH);
        declContainer.setBorder(BorderFactory.createEmptyBorder(0, 10, 10, 10));
        declContainer.setPreferredSize(new Dimension(250, 0));

        return declContainer;
    }

    private JPanel createPostConditionView() {
        final JPanel postCondContainer = new JPanel(new BorderLayout());

        final JLabel titleLabel = new JLabel("Post Condition");
        final JPanel titleLabelContainer = new JPanel(new FlowLayout(FlowLayout.CENTER));
        titleLabelContainer.add(titleLabel);
        postCondContainer.add(titleLabelContainer, BorderLayout.NORTH);

        postCondContainer.add(postCondTextField, BorderLayout.CENTER);

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
            plusButton.setEnabled(true);
            minusButton.setEnabled(true);
            editButton.setEnabled(true);
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
            plusButton.setEnabled(true);
            minusButton.setEnabled(true);
            editButton.setEnabled(true);
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

        final JList<String> locsetDeclsList = new JList<>();
        final JScrollPane scrollPane = new JScrollPane();
        scrollPane.setViewportView(locsetDeclsList);
        result.add(scrollPane, BorderLayout.CENTER);

        locsetDeclsList.setModel(locsetDeclsListModel);

        final JButton plusButton = new JButton(
                IconFontSwing.buildIcon(FontAwesomeSolid.PLUS, 16, Color.BLACK));
        plusButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                final String ls = LocsetInputDialog.showInputDialog(AERelationalDialog.this,
                        services);
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
                    final String selectedElem = locsetDeclsList.getSelectedValue();
                    final String ls = LocsetInputDialog.showInputDialog( //
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
            plusButton.setEnabled(true);
            minusButton.setEnabled(true);
            editButton.setEnabled(true);
        });

        final JPanel buttonsPanel = new JPanel(new FlowLayout(FlowLayout.CENTER));
        buttonsPanel.add(plusButton);
        buttonsPanel.add(editButton);
        buttonsPanel.add(minusButton);

        result.add(buttonsPanel, BorderLayout.SOUTH);
        return result;
    }

    private JComponent createJavaEditorViewLeft() {
        codeLeft.setSyntaxEditingStyle(SyntaxConstants.SYNTAX_STYLE_JAVA);
        codeLeft.setCodeFoldingEnabled(true);

        final JavaErrorParser errorParser = new JavaErrorParser();
        programVariablesChangedListeners.add(errorParser::setProgVarDecls);

        codeLeft.addParser(errorParser);
        return new RTextScrollPane(codeLeft);
    }

    private JComponent createJavaEditorViewRight() {
        codeRight.setSyntaxEditingStyle(SyntaxConstants.SYNTAX_STYLE_JAVA);
        codeRight.setCodeFoldingEnabled(true);

        final JavaErrorParser errorParser = new JavaErrorParser();
        programVariablesChangedListeners.add(errorParser::setProgVarDecls);

        codeRight.addParser(errorParser);
        return new RTextScrollPane(codeRight);
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
    private static interface ProgramVariablesChangedListener {
        public void programVariablesChanged(Collection<ProgramVariableDeclaration> newVars);
    }
}
