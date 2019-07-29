package org.key_project.script.ui;

import bibliothek.gui.dock.common.action.CButton;
import bibliothek.gui.dock.common.action.CDropDownButton;
import com.google.common.base.Strings;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.docking.DockingHelper;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.proof.Proof;
import edu.kit.iti.formal.psdbg.LabelFactory;
import edu.kit.iti.formal.psdbg.interpreter.InterpreterBuilder;
import edu.kit.iti.formal.psdbg.interpreter.KeyInterpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.dbg.*;
import edu.kit.iti.formal.psdbg.interpreter.exceptions.InterpreterRuntimeException;
import edu.kit.iti.formal.psdbg.lint.LintProblem;
import edu.kit.iti.formal.psdbg.lint.LinterStrategy;
import edu.kit.iti.formal.psdbg.parser.Facade;
import edu.kit.iti.formal.psdbg.parser.ScriptLexer;
import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import lombok.Getter;
import lombok.val;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CodePointCharStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.fife.io.DocumentReader;
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.parser.AbstractParser;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParseResult;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParserNotice;
import org.fife.ui.rsyntaxtextarea.parser.ParseResult;
import org.jetbrains.annotations.NotNull;
import org.key_project.editor.Editor;
import org.key_project.ui.interactionlog.InteractionRecorder;
import org.key_project.ui.interactionlog.api.Interaction;
import org.key_project.util.RandomName;

import javax.swing.*;
import javax.swing.Timer;
import javax.swing.*;
import javax.swing.text.BadLocationException;
import javax.swing.text.Document;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.io.IOException;
import java.nio.file.*;
import java.util.*;
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
    private final String name = RandomName.getRandomName("-") + ".kps";
    @Getter
    private final KeyAction actionImportFromInteractionLog = new ImportFromInteractionLog();
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
    private KeyAction actionRebindProof = new RebindProofAction();
    @Getter
    private KeyAction actionClearProofBinding = new ClearProofBindingAction();
    private Proof boundProof;
    private PropertyChangeSupport changeSupport = new PropertyChangeSupport(this);

    public ScriptEditor() {
        setMimeType(ScriptUtils.KPS_LANGUAGE_ID);
        getDockable().setTitleText(name);
        editor.setAntiAliasingEnabled(true);
        editor.setCloseCurlyBraces(true);
        editor.setCloseMarkupTags(true);
        editor.setCodeFoldingEnabled(true);
        editor.addParser(lintParser);
        editor.setText("auto; \n\n//To call subscripts simply add \n//script name(){command;} \n//and call it top level using name;");
        ScriptUtils.createAutoCompletion().install(editor);
        gutter.setBookmarkIcon(BOOKMARK_ICON);
        gutter.setBookmarkingEnabled(true);

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
        });
        updateBoundProof();

        val more = new CDropDownButton("",IconFactory.CONFIGURE.get());
        more.add(DockingHelper.translateAction(actionToggleComment));
        more.add(DockingHelper.translateAction(actionSimpleReformat));
        more.add(DockingHelper.translateAction(actionCasesFromGoals));
        more.add(DockingHelper.translateAction(actionImportFromInteractionLog));
        addAction(more);

        actionToggleComment.registerIn(getEditor());
        actionSimpleReformat.registerIn(getEditor());
        actionCasesFromGoals.registerIn(getEditor());

        mediator.addKeYSelectionListener(this);

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
        if(throwable instanceof  InterpreterRuntimeException){
            onRuntimeError(keyDataDebuggerFramework, (InterpreterRuntimeException) throwable);
        }
        window.popupWarning(throwable.getMessage(), "Interpreting Error");
        throwable.printStackTrace();
        enableGui();
    }

    public void onRuntimeError(DebuggerFramework<KeyData> keyDataDebuggerFramework,
                               InterpreterRuntimeException throwable) {
        throwable.printStackTrace();
        lintParser.getRuntimeException().add(
                new DefaultParserNotice(lintParser, throwable.getMessage(),
                        0, 0, 10));
            String msg = "There was an error while interpreting script";
            if(throwable.getMessage().equals("")){
                msg = throwable.getMessage();
            }
            ASTNode<ParserRuleContext> scriptASTNode = throwable.getScriptASTNode();
            if(scriptASTNode != null){
                msg+= " in statement line "+ scriptASTNode.getStartPosition().getLineNumber();
                try {
                    org.fife.ui.rsyntaxtextarea.Token tokenListForLine = getEditor().getTokenListForLine(scriptASTNode.getStartPosition().getLineNumber() - 1);
                    System.out.println("tokenListForLine = " + tokenListForLine);
                    getEditor().addLineHighlight(scriptASTNode.getStartPosition().getLineNumber()-1, Color.RED);
                } catch (BadLocationException e) {
                    e.printStackTrace();
                }

            }
            window.popupWarning(msg, "Interpreting Error");
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

    private DebuggerFramework<?> getDebuggerFramework() {
        return mediator.get(DebuggerFramework.class);
    }

    private void setDebuggerFramework(DebuggerFramework<?> framework) {
        mediator.deregister(getDebuggerFramework(), DebuggerFramework.class);
        mediator.register(framework, DebuggerFramework.class);
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
                                "\n" + Strings.repeat(" ", nested * 4)));
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
        Token tok; int toktype;
        do {
            tok = lexer.nextToken();
            toktype = tok.getType();
        } while (toktype!= ScriptLexer.SCRIPT && toktype != -1);

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
            setEnabled(getProof() != null
                    && getDebuggerFramework() == null
                    && !mediator.isInAutoMode() &&
                    !getProof().closed());
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            getLintParser().getRuntimeException().clear();
            InterpreterBuilder ib = new InterpreterBuilder();
            try {
                final ScriptEditor f = ScriptEditor.this;
                final RSyntaxTextArea editor = f.editor;
                final CodePointCharStream stream = CharStreams.fromString(editor.getText(), f.getTitle());
                final List<ProofScript> ast = Facade.getAST(stream);

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
                        System.out.println("Breakpoint in ScritpEditor: "+brk);
                        df.getBreakpoints().add(brk);
                    } catch (BadLocationException e1) {
                        e1.printStackTrace();
                    }
                });
                setDebuggerFramework(df);
                disableGui();
                df.setSucceedListener(keyDataDebuggerFramework -> onRunSucceed(keyDataDebuggerFramework));
                df.setErrorListener((keyDataDebuggerFramework, throwable) -> {
                    onRuntimeError(keyDataDebuggerFramework, throwable);
                });
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
            setEnabled(
                    getProof() != null
                            && !getProof().closed()
                            && getDebuggerFramework() != null
                            && getDebuggerFramework().getStatePointer().getStepOver() != null
                            && !getDebuggerFramework().getBreakpoints().isEmpty());
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
                    String s = Files.readString(getPath());
                    setText(s);
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        }
    }

    private class ImportFromInteractionLog extends KeyAction {
        private Interaction lastInteraction = null;

        public ImportFromInteractionLog() {
            setName("Import from interaction log");
            setTooltip("Import the last (unimported) interaction into this buffer.");
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
            if(log == null) return;
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

class LintParser extends AbstractParser {
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
        DocumentReader dr = new DocumentReader(doc);
        try {
            List<ProofScript> scripts = Facade.getAST(CharStreams.fromReader(dr));
            LinterStrategy ls = LinterStrategy.getDefaultLinter();
            if (scriptEditor.getProof() != null) {
                InterpreterBuilder ib = new InterpreterBuilder();
                ib.proof(null, scriptEditor.getProof())
                        .macros()
                        .scriptCommands();
                ls.getCheckers().add(new CallLinter(ib.getLookup()));
            }


            List<LintProblem> problems = ls.check(scripts);

            runtimeException.forEach(result::addNotice);

            for (LintProblem lp : problems) {
                result.addNotice(new DefaultParserNotice(this,
                        lp.getMessage(), lp.getLineNumber(),
                        lp.getFirstToken().getStartIndex(),
                        lp.getFirstToken().getText().length()));
            }

            //TODO result.setParsedLines();
        } catch (IOException | NullPointerException e) {
            result.setError(e);
            e.printStackTrace();
        }

        return result;
    }
}
