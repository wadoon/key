package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.scripts.ScriptView;

import java.awt.event.ActionEvent;

/**
 * Created by sarah on 1/31/17.
 */
public class GoToNodeAction extends AbstractScriptAction {

    private static final String name = "Show in proof tree";

    private ScriptView view;



    public GoToNodeAction(ScriptView view){
        super(name, view);
        this.view = view;

    }

    @Override
    public void actionPerformed(ActionEvent actionEvent) {
        int pos = view.getTextArea().getCaretPosition();
        view.goTo(pos);
    }


}
