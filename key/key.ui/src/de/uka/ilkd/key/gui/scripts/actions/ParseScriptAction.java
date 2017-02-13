package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.scripts.ActualScript;
import de.uka.ilkd.key.gui.scripts.ScriptView;
import de.uka.ilkd.key.macros.scripts.ScriptException;

import java.awt.event.ActionEvent;
import java.io.IOException;
import java.io.StringReader;

/**
 * Created by sarah on 2/6/17.
 */
public class ParseScriptAction extends AbstractScriptAction {

    private ScriptView view;

    private ActualScript script;

    public static final String name = "Parse Script";
    public ParseScriptAction(ScriptView view){
        super(name, view);
        this.script = view.getCurrentScript();
        this.view = view;
    }

    /**
     * Parse a script and set the textual representation
     * @param actionEvent
     */
    @Override
    public void actionPerformed(ActionEvent actionEvent) {

        try {
            this.script = view.getCurrentScript();
            String text = view.getTextArea().getText();
            script.setTextReprOfScript(text);
            script.parse(new StringReader(text));

        } catch (IOException e) {
            e.printStackTrace();
        } catch (ScriptException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }


}
