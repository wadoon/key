package org.key_project.script.ui;

import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import edu.kit.iti.formal.psdbg.lint.LintProblem;
import edu.kit.iti.formal.psdbg.lint.LinterStrategy;
import edu.kit.iti.formal.psdbg.parser.Facade;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import lombok.Getter;
import org.antlr.v4.runtime.CharStreams;
import org.fife.io.DocumentReader;
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.RSyntaxUtilities;
import org.fife.ui.rsyntaxtextarea.parser.AbstractParser;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParseResult;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParserNotice;
import org.fife.ui.rsyntaxtextarea.parser.ParseResult;
import org.fife.ui.rtextarea.Gutter;
import org.fife.ui.rtextarea.RTextScrollPane;
import org.key_project.util.RandomName;

import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import java.awt.*;
import java.io.File;
import java.io.IOException;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (06.03.19)
 */
class ScriptEditorPane extends JPanel {
    public static final String PROP_DIRTY = "dirty";
    public static final String PROP_FILE = "file";
    public static final Icon BOOKMARK_ICON
            = IconFontSwing.buildIcon(FontAwesomeSolid.CIRCLE, 12, Color.red);

    @Getter
    private final RSyntaxTextArea editor;
    @Getter
    private final Gutter gutter;
    @Getter
    private final RTextScrollPane editorView;
    private final String name = RandomName.getRandomName("-") + ".kps";

    @Getter
    private File file;

    @Getter
    private boolean dirty;

    public ScriptEditorPane() {
        super(new BorderLayout(5, 5));
        editor = new RSyntaxTextArea();
        editorView = new RTextScrollPane(editor);
        gutter = RSyntaxUtilities.getGutter(editor);
        editor.setAntiAliasingEnabled(true);
        editor.setCloseCurlyBraces(true);
        editor.setCloseMarkupTags(true);
        editor.setCodeFoldingEnabled(true);
        editor.setSyntaxEditingStyle(ScriptUtils.KPS_LANGUAGE_ID);
        editor.addParser(new LintParser());
        editor.setText("script main() {auto;}\n");
        ScriptUtils.createAutoCompletion().install(editor);
        editor.getDocument().addDocumentListener(new DocumentListener() {
            @Override
            public void insertUpdate(DocumentEvent e) {
                update();
            }

            private void update() {
                setDirty(true);
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
        gutter.setBookmarkIcon(BOOKMARK_ICON);
        gutter.setBookmarkingEnabled(true);
        add(editorView);
    }

    public String getTitle() {
        return (file != null ? file.getName() : name) + (dirty ? "*" : "");
    }

    public String getText() {
        return editor.getText();
    }

    public void setDirty(boolean dirty) {
        boolean oldDirty = isDirty();
        this.dirty = dirty;
        firePropertyChange(PROP_DIRTY, oldDirty, dirty);
    }

    public void setFile(File f) {
        File oldFile = file;
        file = f;
        firePropertyChange(PROP_FILE, oldFile, f);
    }

    private class LintParser extends AbstractParser {
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
            } catch (IOException e ) {
                result.setError(e);
            }
           /* } catch (NullPointerException npe){
                result.setError(npe);
            }*/


            return result;
        }
    }
}
