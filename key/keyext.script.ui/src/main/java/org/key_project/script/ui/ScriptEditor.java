package org.key_project.script.ui;

import com.google.common.base.Strings;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.proof.Proof;
import edu.kit.iti.formal.psdbg.LabelFactory;
import edu.kit.iti.formal.psdbg.interpreter.Interpreter;
import edu.kit.iti.formal.psdbg.interpreter.InterpreterBuilder;
import edu.kit.iti.formal.psdbg.interpreter.KeyInterpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.dbg.*;
import edu.kit.iti.formal.psdbg.interpreter.exceptions.InterpreterRuntimeException;
import edu.kit.iti.formal.psdbg.lint.Level;
import edu.kit.iti.formal.psdbg.lint.LintProblem;
import edu.kit.iti.formal.psdbg.lint.LinterStrategy;
import edu.kit.iti.formal.psdbg.parser.Facade;
import edu.kit.iti.formal.psdbg.parser.ScriptLanguageParser;
import edu.kit.iti.formal.psdbg.parser.ScriptLexer;
import edu.kit.iti.formal.psdbg.parser.TransformAst;
import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import lombok.Getter;
import lombok.val;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.ATNConfigSet;
import org.antlr.v4.runtime.dfa.DFA;
import org.fife.io.DocumentReader;
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.parser.*;
import org.jetbrains.annotations.NotNull;
import org.key_project.editor.Editor;
import org.key_project.ui.interactionlog.InteractionRecorder;
import org.key_project.ui.interactionlog.api.Interaction;
import org.key_project.util.RandomName;

import javax.swing.Timer;
import javax.swing.*;
import javax.swing.text.BadLocationException;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.io.IOException;
import java.nio.file.*;
import java.util.List;
import java.util.*;
import java.util.regex.Pattern;

/**
 * @author Alexander Weigl
 * @version 1 (06.03.19)
 */
class ScriptEditor extends Editor implements KeYSelectionListener {
    public static final String MENU_PROOF_SCRIPTS = "Proof.Scripts";
    public static final float ICON_SIZE = 16;
    public static final String MENU_PROOF_SCRIPTS_EXEC = MENU_PROOF_SCRIPTS + ".Run";
    public static final Icon BOOKMARK_ICON = IconFontSwing.buildIcon(FontAwesomeSolid.CIRCLE, 12, Color.red);
    private static final IconFontProvider ICON_REBIND_PROOF = new IconFontProvider(FontAwesomeSolid.LINK);
    private static final IconFontProvider ICON_CLEAR_BOUND_PROOF = new IconFontProvider(FontAwesomeSolid.UNLINK);
    private static final IconFontProvider ICON_HAMBURGER = new IconFontProvider(FontAwesomeSolid.BARS);
    @Getter
    private final ImportFromInteractionLogAction actionImportFromInteractionLog = new ImportFromInteractionLogAction();
    private final KeyAction actionToggleComment = new ToggleCommentAction();
    @Getter
    LintParser lintParser = new LintParser(this);
    private MainWindow window = MainWindow.getInstance();
    private KeYMediator mediator = window.getMediator();
    @Getter
    private ExecuteAction actionExecute = new ExecuteAction();
    @Getter
    private StepOverAction actionStepOver = new StepOverAction();
    @Getter
    private StopAction actionStop = new StopAction();
    @Getter
    private SimpleReformatAction actionSimpleReformat = new SimpleReformatAction();
    @Getter
    private CreateCasesFromOpenGoalsAction actionCasesFromGoals = new CreateCasesFromOpenGoalsAction();
    @Getter
    private ContinueAction actionContinue = new ContinueAction();
    @Getter
    private LockAndAutoReloadAction actionLockAndAutoReload = new LockAndAutoReloadAction();
    private JLabel lblBoundProof = new JLabel();
    @Getter
    private RebindProofAction actionRebindProof = new RebindProofAction();
    @Getter
    private ClearProofBindingAction actionClearProofBinding = new ClearProofBindingAction();
    private Proof boundProof;
    private PropertyChangeSupport changeSupport = new PropertyChangeSupport(this);
    private HaltListener haltListener = new HaltListener() {
        @Override
        public <T> void onContinue(Interpreter<T> interpreter) {
            setActionEnable();
            disableGui();
        }

        @Override
        public <T> void onHalt(Interpreter<T> interpreter) {
            setActionEnable();
            enableGui();
        }
    };
    /**
     * Bookeeping that a line highlight is not changed if ptreenode was exited
     */
    private PTreeNode currentNode = null;


    public ScriptEditor() {
        super(RandomName.getRandomName("-") + ".kps");
        setMimeType(ScriptUtils.KPS_LANGUAGE_ID);
        getDockable().setTitleText(getTitle());
        editor.setAntiAliasingEnabled(true);
        editor.setCloseCurlyBraces(true);
        editor.setCloseMarkupTags(true);
        editor.setCodeFoldingEnabled(true);
        editor.addParser(lintParser);
        editor.setText("auto; \n\n//To call subscripts simply add \n//script name(){command;} \n//and call it top level using name;");
        ScriptUtils.createAutoCompletion().install(editor);
        gutter.setBookmarkIcon(BOOKMARK_ICON);
        gutter.setBookmarkingEnabled(true);

        layoutToolbar();

        actionToggleComment.registerIn(getEditor());
        actionSimpleReformat.registerIn(getEditor());
        actionCasesFromGoals.registerIn(getEditor());

        mediator.addKeYSelectionListener(this);
        setActionEnable();
    }

    private void layoutToolbar() {
        toolBarActions.add(actionExecute);
        toolBarActions.add(actionContinue);
        toolBarActions.add(actionStepOver);
        toolBarActions.add(actionStop);

        toolBarActions.addSeparator();
        toolBarActions.add(new JLabel("Proof:"));
        toolBarActions.add(lblBoundProof);
        toolBarActions.add(actionRebindProof);
        toolBarActions.add(actionClearProofBinding);
        addPropertyChangeListener("boundProof", e -> {
            updateBoundProof();
            setActionEnable();
        });
        updateBoundProof();

        JPopupMenu menu = new JPopupMenu();
        JButton btnMore = new JButton(ICON_HAMBURGER.get());
        menu.add((actionToggleComment));
        menu.add((actionSimpleReformat));
        menu.add((actionCasesFromGoals));
        menu.add((actionImportFromInteractionLog));
        btnMore.addActionListener(e ->
                menu.show(btnMore, btnMore.getWidth(), btnMore.getHeight()));
        toolBarActions.add(Box.createHorizontalGlue());
        toolBarActions.add(btnMore);
    }

    private void updateBoundProof() {
        if (boundProof == null)
            lblBoundProof.setText("<selected>");
        else
            lblBoundProof.setText(boundProof.name().toString());
    }

    /**
     * Run if debugger framework was able to finish interpreting the proof script
     *
     * @param keyDataDebuggerFramework
     */
    public void onRunSucceed(DebuggerFramework<KeyData> keyDataDebuggerFramework) {

        window.setStatusLine("Interpreting finished");
        editor.setEditable(true);
        enableGui();
        setActionEnable();
    }

    /**
     * Run if debuggerframework encountered errors while interpreting
     *
     * @param keyDataDebuggerFramework
     * @param throwable
     */
    public void onRuntimeError(DebuggerFramework<KeyData> keyDataDebuggerFramework,
                               Throwable throwable) {

        if (throwable instanceof InterpreterRuntimeException) {
            onRuntimeError(keyDataDebuggerFramework, (InterpreterRuntimeException) throwable);
        } else {
            window.popupWarning(throwable.getMessage(), "Interpreting Error");
            throwable.printStackTrace();
        }
        getContentPane().add(new JTextArea(throwable.getMessage(), 5, 40), BorderLayout.SOUTH);
        editor.setEditable(true);
        enableGui();
        setActionEnable();
    }

    public void onRuntimeError(DebuggerFramework<KeyData> keyDataDebuggerFramework,
                               InterpreterRuntimeException throwable) {
        throwable.printStackTrace();
        lintParser.getRuntimeException().clear();
        lintParser.getRuntimeException().add(
                new DefaultParserNotice(lintParser, throwable.getMessage(),
                        0, 0, 10));
        String msg = "There was an error while interpreting script";
        if (throwable.getMessage().equals("")) {
            msg = throwable.getMessage();
        }
        ASTNode<ParserRuleContext> scriptASTNode = throwable.getScriptASTNode();
        if (scriptASTNode != null) {
            msg += " in statement line " + scriptASTNode.getStartPosition().getLineNumber();

        }
        window.popupWarning(msg, "Interpreting Error");
        editor.setEditable(true);
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
        getActionImportFromInteractionLog().setEnabled();
        actionRebindProof.setEnabled();
        actionClearProofBinding.setEnabled();
        getProof();//re-evaluate if the bound proof is still valid.
    }

    private DebuggerFramework<?> getDebuggerFramework() {
        return mediator.get(DebuggerFramework.class);
    }

    private void setDebuggerFramework(DebuggerFramework<?> framework) {
        val old = getDebuggerFramework();
        if (old != null) {
            mediator.deregister(old, DebuggerFramework.class);
            old.removeHaltListener(haltListener);
            old.removeHaltListener(UIScriptExtension.haltListener);
        }
        mediator.register(framework, DebuggerFramework.class);
        framework.addHaltListener(haltListener);
        framework.addHaltListener(UIScriptExtension.haltListener);
        framework.getPtreeManager().getStatePointerListener().add(this::onStatePointerChanged);
    }

    private void onStatePointerChanged(PTreeNode<?> pTreeNode) {
        //ensure that we only highlight once
        if (this.currentNode == null || !this.currentNode.equals(pTreeNode)) {
            this.currentNode = pTreeNode;
            if (pTreeNode.getStatement().getStartPosition().getLineNumber() != -1) {
                try {
                    unHighlightAllExecutionLines();
                    highlightExecutionLine(pTreeNode.getStatement().getStartPosition().getLineNumber() - 1);
                } catch (BadLocationException e) {
                    e.printStackTrace();
                }
            }
        }

    }

    private void highlightStatement(ASTNode statement) throws BadLocationException {
        int lineStartOffset = getEditor().getLineStartOffset(statement.getStartPosition().getLineNumber() - 1);
        highlightRange(statement.getStartPosition().getCharInLine() + lineStartOffset, statement.getEndPosition().getCharInLine() + lineStartOffset, new Color(95, 249, 130));
    }

    private void simpleReformat() {
        Pattern spacesAtLineEnd = Pattern.compile("[\t ]+\n", Pattern.MULTILINE);
        String text = editor.getText();
        text = spacesAtLineEnd.matcher(text).replaceAll("\n");

        ScriptLexer lexer = new ScriptLexer(CharStreams.fromString(text));

        int nested = 0;
        StringBuilder builder = new StringBuilder();
        List<? extends Token> tokens = lexer.getAllTokens();
        for (int i = 0; i < tokens.size(); i++) {
            Token tok = tokens.get(i);
            if (tok.getType() == ScriptLexer.INDENT)
                nested++;

            if (i + 1 < tokens.size() &&
                    tokens.get(i + 1).getType() == ScriptLexer.DEDENT)
                nested--;

            if (tok.getType() == ScriptLexer.WS && tok.getText().startsWith("\n")) {
                builder.append(
                        tok.getText().replaceAll("\n[ \t]*",
                                "\n" + Strings.repeat(" ", Math.max(0, nested * 4))));
            } else {
                builder.append(tok.getText());
            }
        }

        int pos = editor.getCaretPosition();
        setText(builder.toString());
        editor.setCaretPosition(pos);
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {
        //currently do nothing
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        if (mediator.getSelectedProof() != null) {
            setActionEnable();
        }

    }

    public void setBoundProof(Proof boundProof) {
        val old = this.boundProof;
        this.boundProof = boundProof;
        changeSupport.firePropertyChange("boundProof", old, boundProof);
    }

    public void addPropertyChangeListener(PropertyChangeListener listener) {
        changeSupport.addPropertyChangeListener(listener);
    }

    public void removePropertyChangeListener(PropertyChangeListener listener) {
        changeSupport.removePropertyChangeListener(listener);
    }

    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        changeSupport.addPropertyChangeListener(propertyName, listener);
    }

    public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        changeSupport.removePropertyChangeListener(propertyName, listener);
    }

    /**
     * @return the instance on which the script should be executed
     */
    Proof getProof() {
        if (boundProof != null) {
            if (!boundProof.isDisposed()) {
                return boundProof;
            }
            setBoundProof(null);
        }
        return mediator.getSelectedProof();
    }

    private void insertAfterMainPart(String insert) {
        ScriptLexer lexer = new ScriptLexer(CharStreams.fromString(getText()));
        Token tok;
        int toktype;
        do {
            tok = lexer.nextToken();
            toktype = tok.getType();
        } while (toktype != ScriptLexer.SCRIPT && toktype != -1);

        int pos = tok != null ? tok.getStartIndex() : getText().length() - 1;
        editor.insert(insert, pos);
    }

    class ToggleCommentAction extends KeyAction {
        public ToggleCommentAction() {
            setName("Toogle Comment");
            setMenuPath(MENU_PROOF_SCRIPTS);
            setAcceleratorKey(KeyStroke.getKeyStroke("Ctrl+Shift+7"));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            RSyntaxTextArea editor = ScriptEditor.this.editor;
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
            getEditor().setEditable(true);
            DebuggerFramework debuggerFramework = mediator.get(DebuggerFramework.class);
            debuggerFramework.stop();
            try {
                if (debuggerFramework.getInterpreterThread().isAlive()) {
                    debuggerFramework.getInterpreterThread().wait(1000);
                }
            } catch (InterruptedException e1) {

            } finally {
                debuggerFramework.hardStop();
            }
        }

        public void setEnabled() {
            setEnabled(getDebuggerFramework() != null && getDebuggerFramework().getStatePointer().getStepOver() != null);
        }
    }

    class StepOverAction extends KeyAction {
        public StepOverAction() {
            setName("Single Step");
            setMenuPath(MENU_PROOF_SCRIPTS_EXEC);
            setPriority(40);
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.STEP_FORWARD, ICON_SIZE));
            setTooltip("Step over next command");
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
                DebuggerFramework<?> debuggerFramework = getDebuggerFramework();
                if (debuggerFramework != null && debuggerFramework.getInterpreterThread() != null) {
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
            setEnabled((getProof() != null)
                    && ((getDebuggerFramework() == null) ||
                    (getDebuggerFramework().getInterpreterThread().getState() == Thread.State.TERMINATED))
                    && !mediator.isInAutoMode() &&
                    !getProof().closed());
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            getLintParser().getRuntimeException().clear();
            getEditor().setEditable(false);
            InterpreterBuilder ib = new InterpreterBuilder();
            try {
                final ScriptEditor f = ScriptEditor.this;
                final RSyntaxTextArea editor = f.editor;
                final CodePointCharStream stream = CharStreams.fromString(editor.getText(), f.getTitle());
                final List<ProofScript> ast = Facade.getAST(stream);

                if (ast.size() == 0) {
                    return;
                }

                ib.addProofScripts(ast)
                        .proof(null,
                                getProof())
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
                        System.out.println("Breakpoint in ScritpEditor: " + brk);
                        df.getBreakpoints().add(brk);
                    } catch (BadLocationException e1) {
                        e1.printStackTrace();
                    }
                });
                setDebuggerFramework(df);
                disableGui();
                df.setSucceedListener(ScriptEditor.this::onRunSucceed);
                df.setErrorListener(ScriptEditor.this::onRuntimeError);
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
            setTooltip("Continue after breakpoint");
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.FAST_FORWARD, ICON_SIZE));
            setEnabled();
        }

        public void setEnabled() {
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
                if (getDebuggerFramework() != null && getDebuggerFramework().getInterpreterThread() != null) {
                    window.setStatusLine("Continue");
                    disableGui();
                    getDebuggerFramework().execute(new ContinueCommand<>());
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
            Proof proof = getProof();
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
            RSyntaxTextArea editor = ScriptEditor.this.editor;
            editor.insert(s, editor.getCaretPosition());
        }

        public void setEnabled() {
            setEnabled(
                    getProof() != null &&
                            !getProof().closed()
            );
        }
    }

    private class LockAndAutoReloadAction extends KeyAction {
        public LockAndAutoReloadAction() {
            setName("Lock file and auto reload");
            setSelected(true);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            Runnable func = this::update;
            getEditor().setEnabled(!isSelected());
            if (getPath() != null) {
                if (isSelected()) {
                    ModifiedFileWatcherService.getInstance().watch(
                            getPath(), func);
                } else {
                    ModifiedFileWatcherService.getInstance().unwatch(getPath());
                }
            }
        }

        private void update() {
            if (isSelected()) {
                try {
                    assert false;
                    //String s = Files.readString(getPath());
                    //setText(s);
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }
        }
    }

    private class ImportFromInteractionLogAction extends KeyAction {
        private Interaction lastInteraction = null;

        public ImportFromInteractionLogAction() {
            setName("Import from interaction log");
            setTooltip("Import the last (unimported) interaction into this buffer.");
        }

        public void setEnabled() {
            setEnabled(getProof() != null);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            InteractionRecorder recorder = mediator.get(InteractionRecorder.class);
            if (recorder == null) {
                setEnabled(false);
                window.setStatusLine("Could not find interaction log extension.");
                return;
            }
            val log = recorder.get(getProof());
            if (log == null) return;
            val inters = log.getInteractions();
            int startIndex = 0;
            if (lastInteraction != null)
                startIndex = Math.max(0, 1 + inters.lastIndexOf(lastInteraction));
            val sub = inters.subList(startIndex, inters.size());
            StringBuilder sb = new StringBuilder();
            sb.append("// imported from ").append(log.getName()).append("\n");

            for (val inter : sub) {
                sb.append(inter.getProofScriptRepresentation())
                        .append("\n");
                lastInteraction = inter;
            }
            insertAfterMainPart(sb.toString());
        }
    }

    private class RebindProofAction extends KeyAction {
        public RebindProofAction() {
            setName("Bind");
            setTooltip("Bind this editor to the current selected proof.");
            setIcon(ICON_REBIND_PROOF.get());
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            setBoundProof(mediator.getSelectedProof());
        }

        public void setEnabled() {
            setEnabled(mediator.getSelectedProof() != null);
        }
    }

    private class ClearProofBindingAction extends KeyAction {
        public ClearProofBindingAction() {
            setName("Clear");
            setTooltip("Clears the bond to the current proof.");
            setIcon(ICON_CLEAR_BOUND_PROOF.get());
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            setBoundProof(null);
        }

        public void setEnabled() {
            setEnabled(boundProof != null);
        }
    }
}

class ModifiedFileWatcherService implements Runnable {
    private static final WatchService watchService;
    private static ModifiedFileWatcherService SERVICE;

    static {
        WatchService ws = null;
        try {
            ws = FileSystems.getDefault().newWatchService();
        } catch (IOException e) {
            e.printStackTrace();
        }
        watchService = ws;
    }

    private final Map<WatchKey, Runnable> consumers = new HashMap<>();
    private final Map<Path, WatchKey> keys = new HashMap<>();

    private ModifiedFileWatcherService() {
    }

    static ModifiedFileWatcherService getInstance() {
        if (SERVICE == null) {
            SERVICE = new ModifiedFileWatcherService();
            Thread t = new Thread(SERVICE);
            t.setDaemon(true);
            t.start();
        }
        return SERVICE;
    }

    void unwatch(@NotNull Path watch) {
        WatchKey wk = keys.get(watch);
        if (wk != null) {
            wk.cancel();
            consumers.remove(wk);
            keys.remove(watch);
        }
    }

    void watch(@NotNull Path watch, Runnable consumer) {
        try {
            unwatch(watch);
            WatchKey wk = watch.register(watchService, StandardWatchEventKinds.ENTRY_MODIFY);
            consumers.put(wk, consumer);
            keys.put(watch, wk);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void run() {
        while (true) {
            WatchKey wk = watchService.poll();
            consumers.get(wk).run();
        }
    }
}

class LintParser extends AbstractParser implements ANTLRErrorListener {
    private final ScriptEditor scriptEditor;
    @Getter
    private List<DefaultParserNotice> runtimeException = new ArrayList<>(2);
    private DefaultParseResult result = new DefaultParseResult(this);

    LintParser(ScriptEditor editor) {
        this.scriptEditor = editor;
    }

    @Override
    public ParseResult parse(RSyntaxDocument doc, String style) {
        result.clearNotices();
        runtimeException.forEach(result::addNotice);
        DocumentReader dr = new DocumentReader(doc);
        try {
            val stream = CharStreams.fromReader(dr);
            val parser = Facade.getParser(stream);
            parser.removeErrorListeners();
            parser.addErrorListener(this);
            ScriptLanguageParser.StartContext ctx = parser.start();
            if (0 == parser.getNumberOfSyntaxErrors()) {
                val astt = new TransformAst();
                ctx.accept(astt);
                val scripts = astt.getScripts();
                LinterStrategy ls = LinterStrategy.getDefaultLinter();
                if (scriptEditor.getProof() != null) {
                    InterpreterBuilder ib = new InterpreterBuilder();
                    ib.proof(null, scriptEditor.getProof())
                            .macros()
                            .scriptCommands();
                    ls.getCheckers().add(new CallLinter(ib.getLookup()));
                }

                List<LintProblem> problems = ls.check(scripts);
                for (LintProblem lp : problems) {
                    try {
                        System.out.println(lp);
                        DefaultParserNotice notice = new DefaultParserNotice(this,
                                lp.getMessage(), lp.getLineNumber() - 1,
                                lp.getFirstToken().getStartIndex(),
                                lp.getFirstToken().getText().length());
                        if (lp.getIssue().getLevel() == Level.WARN)
                            notice.setLevel(ParserNotice.Level.WARNING);
                        if (lp.getIssue().getLevel() == Level.ERROR)
                            notice.setLevel(ParserNotice.Level.ERROR);
                        if (lp.getIssue().getLevel() == Level.INFO)
                            notice.setLevel(ParserNotice.Level.INFO);
                        result.addNotice(notice);
                    } catch (NullPointerException e) {//linenumber unknown
                    }
                }
            }
        } catch (IOException | NullPointerException e) {
            result.setError(e);
            e.printStackTrace();
        }

        return result;
    }

    @Override
    public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, int charPositionInLine, String msg, RecognitionException e) {
        DefaultParserNotice notice = new DefaultParserNotice(this, msg, line);
        notice.setLevel(ParserNotice.Level.ERROR);
        result.addNotice(notice);
    }

    @Override
    public void reportAmbiguity(Parser recognizer, DFA dfa, int startIndex, int stopIndex, boolean exact, BitSet ambigAlts, ATNConfigSet configs) {
    }

    @Override
    public void reportAttemptingFullContext(Parser recognizer, DFA dfa, int startIndex, int stopIndex, BitSet conflictingAlts, ATNConfigSet configs) {
    }

    @Override
    public void reportContextSensitivity(Parser recognizer, DFA dfa, int startIndex, int stopIndex, int prediction, ATNConfigSet configs) {
    }

    public void clearRuntimeExceptions() {
        this.runtimeException = new ArrayList<>();
    }


}