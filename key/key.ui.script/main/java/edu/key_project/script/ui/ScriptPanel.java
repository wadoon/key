package edu.key_project.script.ui;

import com.google.common.base.Strings;
import de.uka.ilkd.key.api.KeYApi;
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
import lombok.Data;
import lombok.Getter;
import lombok.NonNull;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import org.apache.commons.io.FileUtils;
import org.fife.ui.autocomplete.AutoCompletion;
import org.fife.ui.autocomplete.BasicCompletion;
import org.fife.ui.autocomplete.CompletionProvider;
import org.fife.ui.autocomplete.DefaultCompletionProvider;
import org.fife.ui.rsyntaxtextarea.*;
import org.fife.ui.rsyntaxtextarea.folding.CurlyFoldParser;
import org.fife.ui.rsyntaxtextarea.folding.FoldParserManager;
import org.fife.ui.rsyntaxtextarea.templates.CodeTemplate;
import org.fife.ui.rsyntaxtextarea.templates.StaticCodeTemplate;
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
import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

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
    private final ToggleCommentAction actionToggleAction = new ToggleCommentAction();
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

    private DefaultComboBoxModel<ScriptFile> openFiles = new DefaultComboBoxModel<>();
    private JComboBox<ScriptFile> fileJComboBox = new JComboBox<>(openFiles);
    private JToolBar toolbar;
    private RSyntaxTextArea editor;
    private JFileChooser fileChooser;
    private Gutter gutter;

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
        toolbar.add(fileJComboBox);
        toolbar.addSeparator();
        toolbar.add(actionExecute);


        add(toolbar, BorderLayout.NORTH);
        editor = new RSyntaxTextArea();
        RTextScrollPane editorView = new RTextScrollPane(editor);
        gutter = RSyntaxUtilities.getGutter(editor);
        add(editorView);

        AbstractTokenMakerFactory atmf = (AbstractTokenMakerFactory) TokenMakerFactory.getDefaultInstance();
        atmf.putMapping("text/kps", ProofScriptHighlighter.class.getName());

        FoldParserManager.get().addFoldParserMapping("text/kps", new CurlyFoldParser());

        editor.setAntiAliasingEnabled(true);
        editor.setCloseCurlyBraces(true);
        editor.setCloseMarkupTags(true);
        editor.setCodeFoldingEnabled(true);
        RSyntaxTextArea.setTemplatesEnabled(true);

        CodeTemplateManager ctm = RSyntaxTextArea.getCodeTemplateManager();
        CodeTemplate ct = new StaticCodeTemplate("cc",
                "cases {\n", "\n}");
        ctm.addTemplate(ct);
        ct = new StaticCodeTemplate("fb", "for (int i=0; i<", "; i++) {\n\t\n}\n");
        ctm.addTemplate(ct);

        CompletionProvider provider = createCompletionProvider();
        AutoCompletion ac = new AutoCompletion(provider);
        ac.install(editor);


        editor.setSyntaxEditingStyle("text/kps");
        newScriptFile().setContent("script main() {auto;}\n");
        editor.setText(getCurrentScript().getContent());

        try {
            gutter.setBookmarkIcon(
                    IconFontSwing.buildIcon(FontAwesomeBold.CIRCLE, 12, Color.red)
            );

            gutter.setBookmarkingEnabled(true);
            gutter.addLineTrackingIcon(0, gutter.getBookmarkIcon(), "Bookmark");
        } catch (BadLocationException e) {
            e.printStackTrace();
        }


        fileJComboBox.addActionListener(e -> {
            editor.setText(getCurrentScript().getContent());
        });

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

    /**
     * Create a simple provider that adds some Java-related completions.
     */
    private CompletionProvider createCompletionProvider() {
        DefaultCompletionProvider provider = new DefaultCompletionProvider();

        // Add completions for all Java keywords. A BasicCompletion is just
        // a straightforward word completion.
        String[] words = new String[]{"cases", "case", "try", "closes", "derivable", "default",
                "using", "match", "script", "true", "false", "call", "repeat", "foreach",
                "theonly", "strict", "relax", "while", "if"};
        for (String word : words)
            provider.addCompletion(new BasicCompletion(provider, word));

        KeYApi.getMacroApi().getMacros().forEach(e ->
                provider.addCompletion(new BasicCompletion(provider, e.getScriptCommandName(), "Macro: " + e.getName(),
                        e.getDescription())));

        KeYApi.getScriptCommandApi().getScriptCommands().forEach(e ->
                provider.addCompletion(new BasicCompletion(provider, e.getName(), "Command: " + e.getName(),
                        e.getDocumentation())));

        /*
        provider.addCompletion(new ShorthandCompletion(provider, "sysout",
                "System.out.println(", "System.out.println("));
        provider.addCompletion(new ShorthandCompletion(provider, "syserr",
                "System.err.println(", "System.err.println("));
        */

        return provider;
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
                //no selection
                String s = editor.getText();
                int start = s.lastIndexOf('\n', editor.getCaretPosition()) + 1;
                int stop = s.indexOf('\n', editor.getCaretPosition()) - 1;
                editor.select(start, stop);
            }
            if (isCommented()) {
                String text = editor.getSelectedText();
                text = text.replaceAll("^//\\s?", "");
                editor.replaceSelection(text);
            } else {
                String[] text = editor.getSelectedText().split("\n");
                String newText = Arrays.stream(text).map(s -> "// " + s).collect(Collectors.joining("\n"));
                System.out.println(newText);
                editor.replaceSelection(newText);
            }
            getCurrentScript().setContent(editor.getText());
        }

        private boolean isCommented() {
            String text = editor.getSelectedText().trim();
            String[] lines = text.split("\n");
            return Arrays.stream(lines).allMatch(l -> l.trim().startsWith("//"));
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

@Data
class ScriptFile {
    @NonNull
    private String name;
    private File file;
    private String content;
    private boolean dirty;
}
