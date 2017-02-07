package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.scripts.ActualScript;
import de.uka.ilkd.key.gui.scripts.ScriptView;
import de.uka.ilkd.key.macros.scripts.ScriptException;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.io.IOException;
import java.io.StringReader;

/**
 * Created by sarah on 2/6/17.
 */
public class ParseScriptAction extends AbstractAction {

    private ScriptView view;

    private ActualScript script;

    public ParseScriptAction(ScriptView view, ActualScript script){
        this.script = script;
        this.view = view;
    }

    @Override
    public void actionPerformed(ActionEvent actionEvent) {

        try {
            script.parse(new StringReader(view.getTextArea().getText()));
        } catch (IOException e) {
            e.printStackTrace();
        } catch (ScriptException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }


}
