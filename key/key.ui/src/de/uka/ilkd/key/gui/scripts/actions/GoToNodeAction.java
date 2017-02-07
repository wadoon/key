package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.scripts.ActualScript;
import de.uka.ilkd.key.gui.scripts.ScriptView;
import de.uka.ilkd.key.macros.scripts.ScriptNode;
import de.uka.ilkd.key.proof.Node;

import javax.swing.*;
import java.awt.event.ActionEvent;

/**
 * Created by sarah on 1/31/17.
 */
public class GoToNodeAction extends AbstractAction {

    private static final String name = "Show in proof tree";

    ScriptView view;
    ActualScript currentScript;
    public GoToNodeAction(ScriptView view, ActualScript currentScript){
        super(name);
        this.view = view;
        this.currentScript = currentScript;

    }

    @Override
    public void actionPerformed(ActionEvent actionEvent) {
        goTo();

    }


    private void goTo() {
        int pos = view.getTextArea().getCaretPosition();
        if(currentScript.getCurrentRoot() == null)
            ExceptionDialog.showDialog(view.getMainWindow(), new Exception("There is currently no parsed script tree to browse."));

        ScriptNode snode = view.getNodeAtPos(currentScript.getCurrentRoot(), pos);
        if(snode != null) {
            Node proofNode = snode.getProofNode();
            if(proofNode != null) {
                view.getMediator().getSelectionModel().setSelectedNode(proofNode);
            }
        }
    }

}
