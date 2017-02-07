package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.ScriptViewController;

import javax.swing.*;
import java.awt.event.ActionEvent;

/**
 * Created by sarah on 2/6/17.
 */
public class ShowPathAction extends AbstractAction {
    ScriptViewController contr;
    public final static String name = "Show Path";

    public ShowPathAction(ScriptViewController contr){
        super(name);
        this.contr = contr;

    }

    @Override
    public void actionPerformed(ActionEvent actionEvent) {
        //contr.showPath();
    }
}
