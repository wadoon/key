package org.key_project.script.ui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import edu.kit.iti.formal.psdbg.LabelFactory;
import lombok.AllArgsConstructor;
import lombok.Getter;
import org.key_project.editor.EditorFacade;

import java.awt.*;
import java.awt.datatransfer.Clipboard;
import java.awt.datatransfer.StringSelection;
import java.awt.event.ActionEvent;
import java.io.File;
import java.nio.file.Path;
import java.util.Set;
import java.util.TreeSet;

/**
 * @author Alexander Weigl
 * @version 1 (01.03.19)
 */
@AllArgsConstructor
public class Actions {
    private static final String MENU_PROOF_SCRIPTS_COPY = ScriptEditor.MENU_PROOF_SCRIPTS + ".Copy labels";

    private final MainWindow window;
    private final KeYMediator mediator;

    @Getter
    private final CopyNodePathBranchLabelsAction copyNodePathBranchLabelsAction = new CopyNodePathBranchLabelsAction();
    @Getter
    private final CopyNodePathLineNumbersAction copyNodePathLineNumbersAction = new CopyNodePathLineNumbersAction();
    @Getter
    private final CopyNodePathProgramStatementsAction copyNodePathProgramStatementsAction = new CopyNodePathProgramStatementsAction();
    @Getter
    private final CopyNodePathRuleNamesAction copyNodePathRuleNamesAction = new CopyNodePathRuleNamesAction();
    @Getter
    private final AutoLoadProofScriptAction autoLoadProofScriptAction = new AutoLoadProofScriptAction();

    private void saveToClipboard(String label) {
        System.err.println(label);
        Clipboard clipboard = Toolkit.getDefaultToolkit().getSystemClipboard();
        clipboard.setContents(new StringSelection(label), null);
    }

    class CopyNodePathBranchLabelsAction extends KeyAction {
        public CopyNodePathBranchLabelsAction() {
            setName("Branch labels");
            setMenuPath(MENU_PROOF_SCRIPTS_COPY);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            saveToClipboard(LabelFactory.getBranchingLabel(mediator.getSelectedNode()));
            window.setStatusLine("Branch label copied");
        }
    }

    class CopyNodePathLineNumbersAction extends KeyAction {
        public CopyNodePathLineNumbersAction() {
            setName("Line numbers");
            setMenuPath(MENU_PROOF_SCRIPTS_COPY);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            saveToClipboard(LabelFactory.getProgramLines(mediator.getSelectedNode()));
            window.setStatusLine("Line numbers copied");
        }
    }

    class CopyNodePathRuleNamesAction extends KeyAction {
        public CopyNodePathRuleNamesAction() {
            setName("Rule names");
            setMenuPath(MENU_PROOF_SCRIPTS_COPY);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            saveToClipboard(LabelFactory.getRuleLabel(mediator.getSelectedNode()));
            window.setStatusLine("Rule names copied");
        }
    }

    class CopyNodePathProgramStatementsAction extends KeyAction {
        public CopyNodePathProgramStatementsAction() {
            setName("Program statements");
            setMenuPath(MENU_PROOF_SCRIPTS_COPY);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            saveToClipboard(
                    LabelFactory.getProgramStatmentLabel(mediator.getSelectionModel().getSelectedNode()));
            window.setStatusLine("Program statements copied");
        }
    }

    class AutoLoadProofScriptAction extends KeyAction implements KeYSelectionListener {
        private Set<Integer> loadedProofs = new TreeSet<>();

        public AutoLoadProofScriptAction() {
            setName("Auto open proof script");
            setSelected(true);
            actionPerformed(null);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            if (isSelected()) {
                mediator.addKeYSelectionListener(this);
            } else {
                mediator.removeKeYSelectionListener(this);
            }
        }

        @Override
        public void selectedNodeChanged(KeYSelectionEvent e) {

        }

        @Override
        public void selectedProofChanged(KeYSelectionEvent e) {
            int hash = mediator.getSelectedProof().hashCode();
            File f = mediator.getSelectedProof().getProofFile();
            if (loadedProofs.contains(hash) && f != null) {
                loadedProofs.add(hash);

                String name = f.getName();
                name = name.substring(0, name.lastIndexOf('.'));
                Path path = f.toPath().resolveSibling(
                        name + ".kps"
                );
                if (null == EditorFacade.open(path)) {
                    window.setStatusLine("Could not find a corresponding proof file for proof: " + path);
                }
            }
        }
    }
}
