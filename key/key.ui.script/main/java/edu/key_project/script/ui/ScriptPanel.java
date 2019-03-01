package edu.key_project.script.ui;

import com.google.common.base.Strings;
import com.google.common.io.Files;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeBold;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.proof.Proof;
import edu.kit.iti.formal.psdbg.LabelFactory;
import edu.kit.iti.formal.psdbg.interpreter.InterpreterBuilder;
import edu.kit.iti.formal.psdbg.interpreter.KeyInterpreter;
import edu.kit.iti.formal.psdbg.parser.Facade;
import edu.kit.iti.formal.psdbg.parser.ScriptLanguageLexer;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.NonNull;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import org.apache.commons.io.FileUtils;
import org.fife.ui.rsyntaxtextarea.AbstractTokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.TokenMakerFactory;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;
import javax.swing.filechooser.FileNameExtensionFilter;
import java.awt.*;
import java.awt.event.ActionEvent;
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
    private static final float ICON_SIZE = 12;
    private final MainWindow window;
    private final KeYMediator mediator;

    @Getter
    private final SaveAction actionSave = new SaveAction();
    @Getter
    private final SaveAsAction actionSaveAs = new SaveAsAction();
    @Getter
    private final LoadAction actionLoad = new LoadAction();
    @Getter
    private final ExecuteAction actionExecute = new ExecuteAction();
    @Getter
    private final SimpleReformatAction actionSimpleReformat = new SimpleReformatAction();
    @Getter
    private final CreateCasesFromOpenGoalsAction actionCasesFromGoals = new CreateCasesFromOpenGoalsAction();

    private JToolBar toolbar;
    private RSyntaxTextArea editor;
    private JFileChooser fileChooser;

    public ScriptPanel(MainWindow window, KeYMediator mediator) {
        this.window = window;
        this.mediator = mediator;
        init();
    }

    private void init() {
        setLayout(new BorderLayout());
        toolbar = new JToolBar();
        toolbar.add(actionLoad);
        toolbar.add(actionSave);
        toolbar.add(actionExecute);

        add(toolbar, BorderLayout.NORTH);
        editor = new RSyntaxTextArea();
        add(new RTextScrollPane(editor));


        AbstractTokenMakerFactory atmf = (AbstractTokenMakerFactory) TokenMakerFactory.getDefaultInstance();
        atmf.putMapping("text/kps", ProofScriptHighlighter.class.getName());

        editor.setAntiAliasingEnabled(true);
        editor.setCloseCurlyBraces(true);
        editor.setCloseMarkupTags(true);
        editor.setCodeFoldingEnabled(true);
        editor.setSyntaxEditingStyle("text/kps");

        editor.setText("script main() {auto;}\n");
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
            Files.write(editor.getText().getBytes(), f);
        } catch (IOException e1) {
            window.popupWarning("Could not save to file " + f + ". " + e1.getMessage(),
                    "I/O Error.");
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
            if (getFileChooser().getSelectedFile() != null) {
                storeInto(getFileChooser().getSelectedFile());
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
                    String s = FileUtils.readFileToString(getFileChooser().getSelectedFile(), Charset.defaultCharset());
                    editor.setText(s);
                } catch (IOException e1) {
                    window.popupWarning("Could not load file: " + getFileChooser().getSelectedFile() + ". " + e1.getMessage(), "I/O Error");
                }
            }
        }
    }

    class ExecuteAction extends KeyAction {
        public ExecuteAction() {
            setName("Execute Script");
            setMenuPath(MENU_PROOF_SCRIPTS);
            setIcon(IconFontSwing.buildIcon(FontAwesomeBold.PLAY_CIRCLE, ICON_SIZE));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            InterpreterBuilder ib = new InterpreterBuilder();
            try {
                List<ProofScript> ast = Facade.getAST(editor.getText());

                ib.addProofScripts(ast)
                        .proof(null,
                                mediator.getSelectedProof())
                        .startWith(ast.get(0))
                        .macros()
                        .scriptCommands()
                        .startState();

                KeyInterpreter keyInterpreter = ib.build();
                keyInterpreter.interpret(ib.getEntryPoint());
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
                    for (; true; upperLimit++) {
                        for (String[] lbl : labels) {
                            if (!lbl[upperLimit].equals(ref[upperLimit])) {
                                break;
                            }
                        }
                        upperLimit++;
                    }
                } catch (ArrayIndexOutOfBoundsException ex) {
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
    }
}
