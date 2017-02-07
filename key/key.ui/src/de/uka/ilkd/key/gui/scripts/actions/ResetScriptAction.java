package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.scripts.ActualScript;
import de.uka.ilkd.key.gui.scripts.ScriptView;

import javax.swing.*;
import java.awt.event.ActionEvent;

/**
 * Created by sarah on 2/6/17.
 */
public class ResetScriptAction extends AbstractAction {

    private final ActualScript currentScript;
    private ScriptView view;
    public ResetScriptAction(ScriptView view, ActualScript currentScript){
        this.currentScript = currentScript;
        this.view = view;
    }

    @Override
    public void actionPerformed(ActionEvent actionEvent) {
        currentScript.setAssociatedProof(view.getMediator().getSelectedProof());
        currentScript.setCurrentRoot(null);
    }
}
