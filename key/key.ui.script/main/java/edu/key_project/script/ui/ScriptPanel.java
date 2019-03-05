package edu.key_project.script.ui;

import com.google.common.base.Strings;
import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeBold;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import edu.kit.iti.formal.psdbg.LabelFactory;
import edu.kit.iti.formal.psdbg.interpreter.InterpreterBuilder;
import edu.kit.iti.formal.psdbg.interpreter.KeyInterpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.dbg.Breakpoint;
import edu.kit.iti.formal.psdbg.interpreter.dbg.DebuggerException;
import edu.kit.iti.formal.psdbg.interpreter.dbg.DebuggerFramework;
import edu.kit.iti.formal.psdbg.interpreter.dbg.StepIntoCommand;
import edu.kit.iti.formal.psdbg.parser.Facade;
import edu.kit.iti.formal.psdbg.parser.ScriptLanguageLexer;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.NonNull;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CodePointCharStream;
import org.antlr.v4.runtime.Token;
import org.apache.commons.io.FileUtils;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.RSyntaxUtilities;
import org.fife.ui.rtextarea.Gutter;
import org.fife.ui.rtextarea.RTextScrollPane;
import org.key_project.util.RandomName;

import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.text.BadLocationException;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Pattern;

/**
 * @author Alexander Weigl
 * @version 1 (01.03.19)
 */
@AllArgsConstructor
public class ScriptPanel extends JPanel {
    public static final String MENU_PROOF_SCRIPTS = "Proof Scripts";
    public static final float ICON_SIZE = 12;
    public static final String MENU_PROOF_SCRIPTS_EXEC = MENU_PROOF_SCRIPTS + ".Run";
    private final MainWindow window;
    private final KeYMediator mediator;


    @Getter
    private final ToggleCommentAction actionToggleAction;
    @Getter
    private final SaveAction actionSave;
    @Getter
    private final SaveAsAction actionSaveAs;
    @Getter
    private final LoadAction actionLoad;
    @Getter
    private final ExecuteAction actionExecute;
    @Getter
    private final StepOverAction actionStepOver;
    @Getter
    private final StopAction actionStop;

    @Getter
    private final SimpleReformatAction actionSimpleReformat;
    @Getter
    private final CreateCasesFromOpenGoalsAction actionCasesFromGoals;
    private final PropertyChangeSupport changeListeners = new PropertyChangeSupport(this);
    private final DefaultComboBoxModel<ScriptFile> openFiles = new DefaultComboBoxModel<>();
    private final JComboBox<ScriptFile> fileJComboBox = new JComboBox<>(openFiles);
    private final JToolBar toolbar;
    private final RSyntaxTextArea editor;
    private final Gutter gutter;
    private final RTextScrollPane editorView;
    private JFileChooser fileChooser;
    @Getter
    private DebuggerFramework<KeyData> debuggerFramework;

    public ScriptPanel(MainWindow window, KeYMediator mediator) {
        this.window = window;
        this.mediator = mediator;
        actionToggleAction = new ToggleCommentAction();
        actionSave = new SaveAction();
        actionSaveAs = new SaveAsAction();
        actionLoad = new LoadAction();
        actionExecute = new ExecuteAction();
        actionSimpleReformat = new SimpleReformatAction();
        actionCasesFromGoals = new CreateCasesFromOpenGoalsAction();
        actionStepOver = new StepOverAction();
        actionStop = new StopAction();

        setActionEnable();
        mediator.getUI().getProofControl().addAutoModeListener(new AutoModeListener() {
            @Override
            public void autoModeStarted(ProofEvent e) {
                setActionEnable();
            }

            @Override
            public void autoModeStopped(ProofEvent e) {
                setActionEnable();
            }
        });
        addPropertyChangeListener(evt -> setActionEnable());
        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                setActionEnable();
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                setActionEnable();
                e.getSource().getSelectedProof().addProofTreeListener(new ProofTreeListener() {
                    @Override
                    public void proofExpanded(ProofTreeEvent e) {
                        setActionEnable();
                    }

                    @Override
                    public void proofIsBeingPruned(ProofTreeEvent e) {
                        setActionEnable();
                    }

                    @Override
                    public void proofPruned(ProofTreeEvent e) {
                        setActionEnable();
                    }

                    @Override
                    public void proofStructureChanged(ProofTreeEvent e) {
                        setActionEnable();

                    }

                    @Override
                    public void proofClosed(ProofTreeEvent e) {
                        setActionEnable();

                    }

                    @Override
                    public void proofGoalRemoved(ProofTreeEvent e) {
                        setActionEnable();

                    }

                    @Override
                    public void proofGoalsAdded(ProofTreeEvent e) {
                        setActionEnable();

                    }

                    @Override
                    public void proofGoalsChanged(ProofTreeEvent e) {
                        setActionEnable();

                    }

                    @Override
                    public void smtDataUpdate(ProofTreeEvent e) {
                        setActionEnable();

                    }

                    @Override
                    public void notesChanged(ProofTreeEvent e) {
                        setActionEnable();
                    }
                });
            }
        });
        mediator.addInterruptedListener(this::setActionEnable);
        toolbar = new JToolBar();
        editor = new RSyntaxTextArea();
        editorView = new RTextScrollPane(editor);
        gutter = RSyntaxUtilities.getGutter(editor);
        init();
    }

    private void init() {
        setLayout(new BorderLayout());
        toolbar.add(actionLoad);
        toolbar.add(actionSave);
        toolbar.add(fileJComboBox);
        toolbar.addSeparator();
        toolbar.add(actionExecute);
        toolbar.add(actionStepOver);
        toolbar.add(actionStop);

        add(toolbar, BorderLayout.NORTH);
        add(editorView);
        editor.setText("def");

        ScriptUtils.registerKPSLanguage();
        editor.setAntiAliasingEnabled(true);
        editor.setCloseCurlyBraces(true);
        editor.setCloseMarkupTags(true);
        editor.setCodeFoldingEnabled(true);
        ScriptUtils.registerCodeTemplates();
        ScriptUtils.createAutoCompletion().install(editor);
        RSyntaxTextArea.setTemplatesEnabled(true);

        editor.setSyntaxEditingStyle(ScriptUtils.KPS_LANGUAGE_ID);
        newScriptFile().setContent("script main() {auto;}\n");
        editor.setText(getCurrentScript().getContent());

        try {
            gutter.setBookmarkIcon(
                    IconFontSwing.buildIcon(FontAwesomeBold.CIRCLE, 12, Color.red));
            gutter.setBookmarkingEnabled(true);
            gutter.addLineTrackingIcon(0, gutter.getBookmarkIcon());
        } catch (BadLocationException e) {
            e.printStackTrace();
        }

        fileJComboBox.addActionListener(e -> editor.setText(getCurrentScript().getContent()));

        editor.getDocument().addDocumentListener(new DocumentListener() {
            @Override
            public void insertUpdate(DocumentEvent e) {
                update();
            }

            private void update() {
                getCurrentScript().setDirty(true);
                getCurrentScript().setContent(editor.getText());
                fileJComboBox.updateUI();
            }

            @Override
            public void removeUpdate(DocumentEvent e) {
                update();
            }

            @Override
            public void changedUpdate(DocumentEvent e) {
                update();
            }
        });

        fileJComboBox.setRenderer(new DefaultListCellRenderer() {
            @Override
            public Component getListCellRendererComponent(JList<?> list, Object value, int index, boolean isSelected, boolean cellHasFocus) {
                ScriptFile sf = (ScriptFile) value;
                String sfx = sf.isDirty() ? "*" : "";
                Component lbl = super.getListCellRendererComponent(list, sf.getName() + sfx, index, isSelected, cellHasFocus);
                return lbl;
            }
        });
    }

    private void simpleReformat() {
        Pattern spacesAtLineEnd = Pattern.compile("[\t ]+\n", Pattern.MULTILINE);
        String text = editor.getText();
        text = spacesAtLineEnd.matcher(text).replaceAll("\n");

        ScriptLanguageLexer lexer = new ScriptLanguageLexer(CharStreams.fromString(text));

        int nested = 0;
        StringBuilder builder = new StringBuilder();
        List<? extends Token> tokens = lexer.getAllTokens();
        for (int i = 0; i < tokens.size(); i++) {
            Token tok = tokens.get(i);
            if (tok.getType() == ScriptLanguageLexer.INDENT)
                nested++;

            if (i + 1 < tokens.size() &&
                    tokens.get(i + 1).getType() == ScriptLanguageLexer.DEDENT)
                nested--;

            if (tok.getType() == ScriptLanguageLexer.WS && tok.getText().startsWith("\n")) {
                builder.append(
                        tok.getText().replaceAll("\n[ \t]*",
                                "\n" + Strings.repeat(" ", nested * 4)));
            } else {
                builder.append(tok.getText());
            }
        }

        int pos = editor.getCaretPosition();
        editor.setText(builder.toString());
        editor.setCaretPosition(pos);
    }

    private @NonNull JFileChooser getFileChooser() {
        if (fileChooser == null) {
            File f;
            if (mediator != null
                    && mediator.getSelectedProof() != null
                    && mediator.getSelectedProof().getProofFile() != null) //weigl: I want kotlin!
                f = mediator.getSelectedProof().getProofFile();
            else f = new File(".");
            fileChooser = new JFileChooser(f);
            fileChooser.setFileFilter(new FileNameExtensionFilter("Proof Scripts", ".kps"));
        }
        return fileChooser;
    }

    private void storeInto(File f) {
        try {
            ScriptFile sf = getCurrentScript();
            sf.setContent(editor.getText());
            sf.setFile(f);
            sf.setName(f.getName());
            sf.setDirty(false);
            FileUtils.write(f, editor.getText(), Charset.defaultCharset());
            fileJComboBox.updateUI();
        } catch (IOException e1) {
            window.popupWarning("Could not save to file " + f + ". " + e1.getMessage(),
                    "I/O Error.");
        }
    }

    private ScriptFile getCurrentScript() {
        return (ScriptFile) openFiles.getSelectedItem();
    }

    private ScriptFile newScriptFile() {
        ScriptFile sf = new ScriptFile(RandomName.getRandomName("-"));
        openFiles.addElement(sf);
        return sf;
    }

    private void select(ScriptFile sf) {
        openFiles.setSelectedItem(sf);
    }

    @Override
    public void addPropertyChangeListener(PropertyChangeListener listener) {
        changeListeners.addPropertyChangeListener(listener);
    }

    @Override
    public void removePropertyChangeListener(PropertyChangeListener listener) {
        changeListeners.removePropertyChangeListener(listener);
    }

    private void setDebuggerFramework(DebuggerFramework<KeyData> df) {
        DebuggerFramework<KeyData> old = debuggerFramework;
        debuggerFramework = df;
        changeListeners.firePropertyChange("debuggerFramework", old, df);

        df.setErrorListener(this::onRuntimeError);
        df.setErrorListener(this::onRunSucceed);
    }

    private void onRunSucceed(DebuggerFramework<KeyData> keyDataDebuggerFramework, Throwable throwable) {
        window.setStatusLine("Interpreting finished");
        enableGui();
    }

    private void onRuntimeError(DebuggerFramework<KeyData> keyDataDebuggerFramework, Throwable throwable) {
        window.popupWarning(throwable.getMessage(), "Interpreting Error");
        enableGui();
    }

    private void disableGui() {
        mediator.stopInterface(true);
    }

    private void enableGui() {
        mediator.startInterface(true);
    }

    public void setActionEnable() {
        getActionExecute().setEnabled();
        getActionStepOver().setEnabled();
        getActionStop().setEnabled();
        getActionCasesFromGoals().setEnabled();
    }

    class ToggleCommentAction extends KeyAction {
        public ToggleCommentAction() {
            setName("Toogle Comment");
            setMenuPath(MENU_PROOF_SCRIPTS);
            setAcceleratorKey(KeyStroke.getKeyStroke("Ctrl+Shift+7"));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            if (editor.getSelectionStart() == editor.getSelectionEnd()) {
                //expand to line start and end.
                String s = editor.getText();
                int start = s.lastIndexOf('\n', editor.getSelectionStart()) + 1;
                int stop = s.indexOf('\n', editor.getSelectionEnd());
                editor.select(start, stop);
            }
            String selected = editor.getSelectedText();
            String newText;
            if (ScriptUtils.isCommented(selected)) {
                newText = ScriptUtils.removeComments(selected);
            } else {
                newText = ScriptUtils.comment(selected);
            }
            editor.replaceSelection(newText); // TODO does not work!
            //getCurrentScript().setContent(editor.getText());
        }

    }

    class SaveAsAction extends KeyAction {
        public SaveAsAction() {
            setName("Save as…");
            setTooltip("Save the current proof scripts");
            setMenuPath(MENU_PROOF_SCRIPTS);
            setIcon(IconFontSwing.buildIcon(FontAwesomeBold.SAVE, ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            int c = getFileChooser().showSaveDialog(ScriptPanel.this);
            if (c == JFileChooser.APPROVE_OPTION) {
                File f = getFileChooser().getSelectedFile();
                storeInto(f);
            }
        }
    }

    class SaveAction extends KeyAction {
        public SaveAction() {
            setName("Save");
            setTooltip("Store script file");
            setMenuPath(MENU_PROOF_SCRIPTS);
            setIcon(IconFontSwing.buildIcon(FontAwesomeBold.DOWNLOAD, ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            if (getCurrentScript().getFile() != null) {
                storeInto(getCurrentScript().getFile());
            } else {
                getActionSaveAs().actionPerformed(e);
            }
        }
    }

    class LoadAction extends KeyAction {
        public LoadAction() {
            setName("Load proof script");
            setIcon(IconFontSwing.buildIcon(FontAwesomeBold.UPLOAD, ICON_SIZE));
            setMenuPath(MENU_PROOF_SCRIPTS);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            int c = getFileChooser().showOpenDialog(ScriptPanel.this);
            if (c == JFileChooser.APPROVE_OPTION) {
                try {
                    File file = getFileChooser().getSelectedFile();
                    String s = FileUtils.readFileToString(file, Charset.defaultCharset());
                    ScriptFile sf = newScriptFile();
                    sf.setContent(s);
                    sf.setFile(file);
                    sf.setName(file.getName());
                    sf.setDirty(false);
                    select(sf);
                } catch (IOException e1) {
                    window.popupWarning("Could not load file: " + getFileChooser().getSelectedFile() + ". " + e1.getMessage(), "I/O Error");
                }
            }
        }
    }

    class StopAction extends KeyAction {
        public StopAction() {
            setName("Stop interpreter");
            setMenuPath(MENU_PROOF_SCRIPTS_EXEC);
            setIcon(IconFontSwing.buildIcon(FontAwesomeBold.STOP_CIRCLE, ICON_SIZE));
            setEnabled();
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            debuggerFramework.stop();
            try {
                debuggerFramework.getInterpreterThread().wait(1000);
            } catch (InterruptedException e1) {

            } finally {
                debuggerFramework.hardStop();
                setDebuggerFramework(null);
            }
        }

        public void setEnabled() {
            setEnabled(getDebuggerFramework() != null);
        }
    }

    class StepOverAction extends KeyAction {
        public StepOverAction() {
            setName("Step Over");
            setMenuPath(MENU_PROOF_SCRIPTS_EXEC);
            setIcon(IconFontSwing.buildIcon(FontAwesomeBold.STEP_FORWARD, ICON_SIZE));

            setEnabled();
            addPropertyChangeListener(evt -> setEnabled());
            Timer timer = new Timer(100, e -> setEnabled());
            timer.setRepeats(true);
            timer.start();
        }

        private void setEnabled() {
            setEnabled(getDebuggerFramework() != null &&
                    getDebuggerFramework().getInterpreterThread() != null &&
                    (getDebuggerFramework().getInterpreterThread().getState() == Thread.State.WAITING
                            || getDebuggerFramework().getInterpreterThread().getState() == Thread.State.BLOCKED
                    ));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            try {
                if (getDebuggerFramework() != null && debuggerFramework.getInterpreterThread() != null) {
                    window.setStatusLine("Step over");
                    debuggerFramework.execute(new StepIntoCommand<>());
                }
            } catch (DebuggerException e1) {
                window.setStatusLine(e1.getMessage());
            }
        }
    }

    class ExecuteAction extends KeyAction {
        public ExecuteAction() {
            setName("Execute Script");
            setMenuPath(MENU_PROOF_SCRIPTS_EXEC);
            setIcon(IconFontSwing.buildIcon(FontAwesomeBold.PLAY_CIRCLE, ICON_SIZE));

            setEnabled();
        }

        private void setEnabled() {
            setEnabled(mediator.getSelectedProof() != null
                    && getDebuggerFramework() == null
                    && !mediator.isInAutoMode() &&
                    !mediator.getSelectedProof().closed());
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            InterpreterBuilder ib = new InterpreterBuilder();
            try {
                CodePointCharStream stream = CharStreams.fromString(editor.getText(), getCurrentScript().getName());
                List<ProofScript> ast = Facade.getAST(stream);

                ib.addProofScripts(ast)
                        .proof(null,
                                mediator.getSelectedProof())
                        .startWith(ast.get(0))
                        .macros()
                        .scriptCommands()
                        .startState();

                KeyInterpreter keyInterpreter = ib.build();
                DebuggerFramework<KeyData> df = new DebuggerFramework<>(
                        keyInterpreter, ib.getEntryPoint(), null
                );
                df.unregister();
                Arrays.stream(gutter.getBookmarks()).forEach(it -> {
                    try {
                        int line = 1 + editor.getLineOfOffset(it.getMarkedOffset());
                        Breakpoint brk = new Breakpoint(getCurrentScript().getName(), line);
                        System.out.println(brk);
                        df.getBreakpoints().add(brk);
                    } catch (BadLocationException e1) {
                        e1.printStackTrace();
                    }
                });
                setDebuggerFramework(df);
                disableGui();
                df.start();
            } catch (Exception e1) {
                e1.printStackTrace();
            }
        }
    }

    class SimpleReformatAction extends KeyAction {
        public SimpleReformatAction() {
            setName("Reformat");
            setMenuPath(MENU_PROOF_SCRIPTS);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            simpleReformat();
        }
    }

    class CreateCasesFromOpenGoalsAction extends KeyAction {
        public CreateCasesFromOpenGoalsAction() {
            setName("Insert cases for open goals");
            setMenuPath(MENU_PROOF_SCRIPTS);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            Proof proof = mediator.getSelectedProof();
            List<String[]> labels = LabelFactory.getLabelOfOpenGoals(proof, LabelFactory::getBranchingLabel);
            String text;
            if (labels.isEmpty()) {
                text = "// no open goals";
            } else if (labels.size() == 1) {
                text = "// only one goal";
            } else {
                int upperLimit = 0;
                /* trying to find the common suffix*/
                try {
                    String[] ref = labels.get(0);
                    for (; upperLimit <= ref.length; upperLimit++) {
                        for (String[] lbl : labels) {
                            if (!lbl[upperLimit].equals(ref[upperLimit])) {
                                break;
                            }
                        }
                    }
                } catch (ArrayIndexOutOfBoundsException ignored) {
                }

                int finalUpperLimit = upperLimit;
                text = labels.stream()
                        .map(a -> Arrays.stream(a, finalUpperLimit, a.length))
                        .map(s -> s.reduce((a, b) -> b + LabelFactory.SEPARATOR + a).orElse("error"))
                        .map(s -> String.format("\tcase match \"%s\" :\n\t\t//commands", s))
                        .reduce((a, b) -> a + "\n" + b)
                        .orElse("ERROR");
            }

            String s = "cases {\n" + text + "\n}";
            editor.insert(s, editor.getCaretPosition());
        }

        public void setEnabled() {
            setEnabled(
                    mediator.getSelectedProof() != null &&
                            !mediator.getSelectedProof().closed()
            );
        }
    }
}

