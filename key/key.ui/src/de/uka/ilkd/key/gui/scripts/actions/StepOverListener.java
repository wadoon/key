package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.scripts.DebugModel;
import de.uka.ilkd.key.gui.scripts.ScriptView;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.macros.scripts.ScriptNode;

import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.List;
/*
rule impRight;
rule impRight;
rule notRight;
rule notLeft;

rule impRight;
rule impLeft;
branches;
	rule impRight;
	rule notLeft;
	rule notRight;
next;
	rule impRight;
	rule notLeft;
	rule notRight;
end;

*/
/**
 * Created by sarah on 2/8/17.
 */
public class StepOverListener extends KeyAdapter {

    private DebugModel model;
    private ScriptView view;

    /**
     * Controller to step over a state in the script
     * @param model
     * @param view
     */
    public StepOverListener(DebugModel model, ScriptView view){
        super();
        this.model = model;
        this.view  = view;

    }

    @Override
    public void keyPressed(KeyEvent keyEvent) {
        super.keyPressed(keyEvent);
        if (keyEvent.getKeyCode() == KeyEvent.VK_F3) {
            view.getTextArea().removeAllLineHighlights();
            view.getTextArea().repaint();
            stepOver();
        }
    }

    private void stepOver(){
        view.getTextArea().removeAllLineHighlights();
        view.getTextArea().repaint();

        List<ScriptNode> state = model.getNextScriptState();
        if (state == null) {
        }

        if(state.size() == 1){
            ScriptNode n = state.get(0);
            int from = n.getFromPos();
            int to = n.getToPos();
            view.getTextArea().highlightLinesatPos(from, to);
            view.getTextArea().setCaretPosition(to);
            view.goTo(to);

        }if(state.size() == 0){
            ExceptionDialog.showDialog(view.getMainWindow(), new ScriptException("There is no parsed script to debug."));
        }
        if(state.size()>1){
            for (ScriptNode scriptNode : state) {
                int from = scriptNode.getFromPos();
                int to = scriptNode.getToPos();
                view.getTextArea().highlightLinesatPos(from, to);
                if(model.getCurrentPointerToScript().equals(scriptNode)){
                    view.getTextArea().setCaretPosition(to);
                    view.goTo(to);
                }
            }
        }

    }
}
