package edu.key_project.script.ui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.proof.Proof;
import edu.kit.iti.formal.psdbg.LabelFactory;
import lombok.AllArgsConstructor;
import lombok.Getter;

import java.awt.*;
import java.awt.datatransfer.Clipboard;
import java.awt.datatransfer.StringSelection;
import java.awt.event.ActionEvent;
import java.util.Arrays;
import java.util.List;

import static edu.key_project.script.ui.ScriptPanel.MENU_PROOF_SCRIPTS;

/**
 * @author Alexander Weigl
 * @version 1 (01.03.19)
 */
@AllArgsConstructor
public class Actions {
    private static final String MENU_PROOF_SCRIPTS_COPY = MENU_PROOF_SCRIPTS + ".Copy labels";

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


    private void saveToClipboard(String label) {
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
        }
    }

}
