package org.key_project.script.ui;

import com.google.common.base.Strings;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.proof.Proof;
import edu.kit.iti.formal.psdbg.LabelFactory;
import edu.kit.iti.formal.psdbg.interpreter.InterpreterBuilder;
import edu.kit.iti.formal.psdbg.interpreter.KeyInterpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.dbg.*;
import edu.kit.iti.formal.psdbg.lint.LintProblem;
import edu.kit.iti.formal.psdbg.lint.LinterStrategy;
import edu.kit.iti.formal.psdbg.parser.Facade;
import edu.kit.iti.formal.psdbg.parser.ScriptLanguageLexer;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import lombok.Getter;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CodePointCharStream;
import org.antlr.v4.runtime.Token;
import org.fife.io.DocumentReader;
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.parser.AbstractParser;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParseResult;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParserNotice;
import org.fife.ui.rsyntaxtextarea.parser.ParseResult;
import org.key_project.editor.Editor;
import org.key_project.util.RandomName;

import javax.swing.*;
import javax.swing.text.BadLocationException;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Pattern;

/**
 * @author Alexander Weigl
 * @version 1 (06.03.19)
 */
class ScriptEditor extends Editor implements KeYSelectionListener {
    public static final String MENU_PROOF_SCRIPTS = "Proof Scripts";
    public static final float ICON_SIZE = 16;
    public static final String MENU_PROOF_SCRIPTS_EXEC = MENU_PROOF_SCRIPTS + ".Run";
    public static final Icon BOOKMARK_ICON = IconFontSwing.buildIcon(FontAwesomeSolid.CIRCLE, 12, Color.red);
    private final String name = RandomName.getRandomName("-") + ".kps";

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


    public ScriptEditor() {
        setMimeType(ScriptUtils.KPS_LANGUAGE_ID);
        getDockable().setTitleText(name);
        editor.setAntiAliasingEnabled(true);
        editor.setCloseCurlyBraces(true);
        editor.setCloseMarkupTags(true);
        editor.setCodeFoldingEnabled(true);
        editor.addParser(new LintParser());
        editor.setText("auto; \n\n \\\\To call subscripts simply add \\\\script name(){command;} and call it top level");
        ScriptUtils.createAutoCompletion().install(editor);
        gutter.setBookmarkIcon(BOOKMARK_ICON);
        gutter.setBookmarkingEnabled(true);

        toolBarActions.add(actionExecute);
        toolBarActions.add(actionContinue);
        toolBarActions.add(actionStepOver);
        toolBarActions.add(actionStop);
        toolBarActions.addSeparator();
        toolBarActions.add(actionSimpleReformat);
        toolBarActions.add(actionCasesFromGoals);

        mediator.addKeYSelectionListener(this);


    }

    /**
     * Run if debugger framework was able to finish interpreting the proof script
     * @param keyDataDebuggerFramework
     */
    public void onRunSucceed(DebuggerFramework<KeyData> keyDataDebuggerFramework) {
        window.setStatusLine("Interpreting finished");
        enableGui();
    }

    /**
     * Run if debuggerframework encountered errors while interpreting
     * @param keyDataDebuggerFramework
     * @param throwable
     */
    public void onRuntimeError(DebuggerFramework<KeyData> keyDataDebuggerFramework, Throwable throwable) {
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
        setText(builder.toString());
        editor.setCaretPosition(pos);
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {
        //currently do nothing
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        if(mediator.getSelectedProof() != null){
           setActionEnable();
        }

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
                debuggerFramework.getInterpreterThread().wait(1000);
            } catch (InterruptedException e1) {

            } finally {
                debuggerFramework.hardStop();
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
            setEnabled(mediator.getSelectedProof() != null
                    && getDebuggerFramework() == null
                    && !mediator.isInAutoMode() &&
                    !mediator.getSelectedProof().closed());
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            InterpreterBuilder ib = new InterpreterBuilder();
            try {
                final ScriptEditor f = ScriptEditor.this;
                final RSyntaxTextArea editor = f.editor;
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
                df.setSucceedListener(keyDataDebuggerFramework -> onRunSucceed(keyDataDebuggerFramework));
                df.setErrorListener((keyDataDebuggerFramework, throwable) -> {
                    onRuntimeError(keyDataDebuggerFramework,throwable);
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
            setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.FAST_FORWARD, ICON_SIZE));
        }

        public void setEnabled() {
            setEnabled(mediator.getSelectedProof() != null && getDebuggerFramework() != null);
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
            RSyntaxTextArea editor = ScriptEditor.this.editor;
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

class LintParser extends AbstractParser {
    private DefaultParseResult result = new DefaultParseResult(this);

    @Override
    public ParseResult parse(RSyntaxDocument doc, String style) {
        result.clearNotices();
        DocumentReader dr = new DocumentReader(doc);
        try {
            List<ProofScript> scripts = Facade.getAST(CharStreams.fromReader(dr));
            LinterStrategy ls = LinterStrategy.getDefaultLinter();
            List<LintProblem> problems = ls.check(scripts);

            for (LintProblem lp : problems) {
                result.addNotice(new DefaultParserNotice(this,
                        lp.getMessage(), lp.getLineNumber(),
                        lp.getFirstToken().getStartIndex(),
                        lp.getFirstToken().getText().length()));
            }

            //TODO result.setParsedLines();
        } catch (IOException | NullPointerException e) {
            result.setError(e);
        }

        return result;
    }
}
