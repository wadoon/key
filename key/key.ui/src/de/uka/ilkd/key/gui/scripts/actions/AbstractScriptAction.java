package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.scripts.ScriptView;

import javax.swing.*;

/**
 * Created by sarah on 2/8/17.
 */
public abstract class AbstractScriptAction extends AbstractAction {

    public ScriptView getView() {
        return view;
    }

    public void setView(ScriptView view) {
        this.view = view;
    }

    private ScriptView view;



    public AbstractScriptAction(String name, ScriptView view){
        super(name);
        this.view = view;
    }




}
