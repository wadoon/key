package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.scripts.ActualScript;
import de.uka.ilkd.key.gui.scripts.ScriptView;

import java.awt.event.ActionEvent;

/**
 * Created by sarah on 2/6/17.
 */
public class ResetScriptAction extends AbstractScriptAction {

    private final ActualScript currentScript;
    private ScriptView view;

    public static final String name ="Reset State";
    public ResetScriptAction(ScriptView view){
        super(name, view);
        this.currentScript = view.getCurrentScript();
        this.view = view;
    }

    @Override
    public void actionPerformed(ActionEvent actionEvent) {
        currentScript.setAssociatedProof(view.getMediator().getSelectedProof());
        currentScript.setCurrentRoot(null);
    }
}
