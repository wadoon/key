package org.key_project.script.ui;

import com.google.common.base.Charsets;
import com.google.common.base.Strings;
import com.google.common.io.Files;
import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import edu.kit.iti.formal.psdbg.LabelFactory;
import edu.kit.iti.formal.psdbg.interpreter.InterpreterBuilder;
import edu.kit.iti.formal.psdbg.interpreter.KeyInterpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.dbg.*;
import edu.kit.iti.formal.psdbg.parser.Facade;
import edu.kit.iti.formal.psdbg.parser.ScriptLanguageLexer;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.NonNull;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CodePointCharStream;
import org.antlr.v4.runtime.Token;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;

import javax.swing.*;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.text.BadLocationException;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.beans.PropertyChangeListener;
import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Pattern;

/**
 * @author Alexander Weigl
 * @version 1 (01.03.19)
 */
@AllArgsConstructor
public class ScriptPanel extends JPanel implements TabPanel {
    public static final String MENU_PROOF_SCRIPTS = "Proof Scripts";
    public static final float ICON_SIZE = 16;
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
    @Getter
    private final ContinueAction actionContinue;

    private final JToolBar toolbar;

    @Getter
    private final JTabbedPane tabbedEditors = new JTabbedPane(
            JTabbedPane.BOTTOM,
            JTabbedPane.SCROLL_TAB_LAYOUT);

    private JFileChooser fileChooser;

    static IconFontProvider ICON_SCRIPT = new IconFontProvider(FontAwesomeSolid.PEN);

    @Getter
    private DebuggerFramework<KeyData> debuggerFramework;
    Timer timer = new Timer(100, e -> {
        boolean flag = getDebuggerFramework() != null &&
                getDebuggerFramework().getInterpreterThread() != null &&
                (getDebuggerFramework().getInterpreterThread().getState() == Thread.State.WAITING
                        || getDebuggerFramework().getInterpreterThread().getState() == Thread.State.BLOCKED
                );
        if (flag) enableGui();
    });
    private PropertyChangeListener updateTitlesListener = evt -> updateTitles();

    public ScriptPanel(MainWindow window, KeYMediator mediator) {
        this.window = window;
        this.mediator = mediator;
        actionToggleAction = new ToggleCommentAction();
        actionSave = new SaveAction();
        actionSaveAs = new SaveAsAction();
        actionLoad = new LoadAction();
        actionExecute = new ExecuteAction();
        actionContinue = new ContinueAction();

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
        init();
        timer.setRepeats(true);
        timer.start();

    }

    private void init() {
        setLayout(new BorderLayout());
        toolbar.add(actionLoad);
        toolbar.add(actionSave);
        //toolbar.add(fileJComboBox);
        toolbar.addSeparator();
        toolbar.add(actionExecute);
        toolbar.add(actionStop);
        toolbar.add(actionContinue);
        toolbar.add(actionStepOver);

        add(toolbar, BorderLayout.NORTH);
        add(tabbedEditors);

        ScriptUtils.registerKPSLanguage();
        ScriptUtils.registerCodeTemplates();
        RSyntaxTextArea.setTemplatesEnabled(true);

        newEditor();
    }

    private void simpleReformat() {
        Pattern spacesAtLineEnd = Pattern.compile("[\t ]+\n", Pattern.MULTILINE);
        String text = getCurrentEditor().getText();
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

        int pos = getCurrentEditor().getEditor().getCaretPosition();
        getCurrentEditor().getEditor().setText(builder.toString());
        getCurrentEditor().getEditor().setCaretPosition(pos);
    }

    private ScriptEditorPane getCurrentEditor() {
        return (ScriptEditorPane) tabbedEditors.getSelectedComponent();
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
            ScriptEditorPane sf = getCurrentEditor();
            sf.setFile(f);
            sf.setDirty(false);
            Files.asCharSink(f, Charsets.UTF_8).write(sf.getEditor().getText());
            updateTitles();
        } catch (IOException e1) {
            window.popupWarning("Could not save to file " + f + ". " + e1.getMessage(),
                    "I/O Error.");
        }
    }

    private void updateTitles() {
        for (int i = 0; i < tabbedEditors.getTabCount(); i++) {
            ScriptEditorPane sf = (ScriptEditorPane) tabbedEditors.getComponentAt(i);
            tabbedEditors.setTitleAt(i, sf.getTitle());
        }
    }

    private ScriptEditorPane newEditor() {
        ScriptEditorPane sep = new ScriptEditorPane();
        tabbedEditors.addTab(sep.getTitle(), sep);
        sep.addPropertyChangeListener(ScriptEditorPane.PROP_DIRTY, updateTitlesListener);
        sep.addPropertyChangeListener(ScriptEditorPane.PROP_FILE, updateTitlesListener);
        return sep;
    }

    private void select(File f) {
        for (int i = 0; i < tabbedEditors.getTabCount(); i++) {
            ScriptEditorPane sf = (ScriptEditorPane) tabbedEditors.getComponentAt(i);
            if (sf.getFile().equals(f)) {
                tabbedEditors.setSelectedComponent(sf);
            }
        }
    }

    private void setDebuggerFramework(DebuggerFramework<KeyData> df) {
        DebuggerFramework<KeyData> old = debuggerFramework;
        debuggerFramework = df;
        firePropertyChange("debuggerFramework", old, df);
        if (old != null) {
            old.removeErrorListener();
            old.removeSucceedListener();
        }
        if (df != null) {
            df.setErrorListener(this::onRuntimeError);
            df.setSucceedListener(this::onRunSucceed);
        }
    }

    private void onRunSucceed(DebuggerFramework<KeyData> keyDataDebuggerFramework) {
        window.setStatusLine("Interpreting finished");
        enableGui();
    }

    private void onRuntimeError(DebuggerFramework<KeyData> keyDataDebuggerFramework, Throwable throwable) {
        window.popupWarning(throwable.getMessage(), "Interpreting Error");
        throwable.printStackTrace();
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
        getActionContinue().setEnabled();
        getActionCasesFromGoals().setEnabled();
    }

    @Override
    public String getTitle() {
        return "Scripting";
    }

    @Override
    public JComponent getComponent() {
        return this;
    }

    class ToggleCommentAction extends KeyAction {
        public ToggleCommentAction() {
            setName("Toogle Comment");
            setMenuPath(MENU_PROOF_SCRIPTS);
            setAcceleratorKey(KeyStroke.getKeyStroke("Ctrl+Shift+7"));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            RSyntaxTextArea editor = getCurrentEditor().getEditor();
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
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.SAVE, ICON_SIZE));
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
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.DOWNLOAD, ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            if (getCurrentEditor().getFile() != null) {
                storeInto(getCurrentEditor().getFile());
            } else {
                getActionSaveAs().actionPerformed(e);
            }
        }
    }

    class LoadAction extends KeyAction {
        public LoadAction() {
            setName("Load proof script");
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.UPLOAD, ICON_SIZE));
            setMenuPath(MENU_PROOF_SCRIPTS);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            int c = getFileChooser().showOpenDialog(ScriptPanel.this);
            if (c == JFileChooser.APPROVE_OPTION) {
                try {
                    File file = getFileChooser().getSelectedFile();
                    String s = Files.asCharSource(file, Charsets.UTF_8).read();
                    ScriptEditorPane editor = newEditor();
                    editor.getEditor().setText(s);
                    editor.setFile(file);
                    editor.setDirty(false);
                    tabbedEditors.setSelectedComponent(editor);
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
            setPriority(10);
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.STOP_CIRCLE, ICON_SIZE, Color.RED));
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
            setName("Single Step");
            setMenuPath(MENU_PROOF_SCRIPTS_EXEC);
            setPriority(40);
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.STEP_FORWARD, ICON_SIZE));

            setEnabled();
            Timer timer = new Timer(250, e -> setEnabled());
            timer.setRepeats(true);
            timer.start();
        }

        private void setEnabled() {
            boolean flag = getDebuggerFramework() != null &&
                    getDebuggerFramework().getInterpreterThread() != null &&
                    (getDebuggerFramework().getInterpreterThread().getState() == Thread.State.WAITING
                            || getDebuggerFramework().getInterpreterThread().getState() == Thread.State.BLOCKED
                    );
            setEnabled(flag);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            try {
                if (getDebuggerFramework() != null && debuggerFramework.getInterpreterThread() != null) {
                    window.setStatusLine("Step over");
                    disableGui();
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
            setPriority(0);
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.PLAY_CIRCLE, ICON_SIZE,
                    new Color(140, 182, 60)));
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
                final ScriptEditorPane f = getCurrentEditor();
                final RSyntaxTextArea editor = getCurrentEditor().getEditor();
                final CodePointCharStream stream = CharStreams.fromString(editor.getText(), f.getTitle());
                final List<ProofScript> ast = Facade.getAST(stream);

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
                Arrays.stream(f.getGutter().getBookmarks()).forEach(it -> {
                    try {
                        int line = 1 + editor.getLineOfOffset(it.getMarkedOffset());
                        Breakpoint brk = new Breakpoint(f.getTitle(), line);
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

    class ContinueAction extends KeyAction {
        public ContinueAction() {
            setName("Continue");
            setMenuPath(MENU_PROOF_SCRIPTS_EXEC);
            setPriority(30);
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.FAST_FORWARD, ICON_SIZE));
        }

        public void setEnabled() {
            setEnabled(mediator.getSelectedProof() != null && debuggerFramework != null);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            try {
                if (getDebuggerFramework() != null && debuggerFramework.getInterpreterThread() != null) {
                    window.setStatusLine("Continue");
                    disableGui();
                    debuggerFramework.execute(new ContinueCommand<>());
                }
            } catch (DebuggerException e1) {
                window.setStatusLine(e1.getMessage());
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
            RSyntaxTextArea editor = getCurrentEditor().getEditor();
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

