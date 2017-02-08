package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.scripts.DebugModel;
import de.uka.ilkd.key.gui.scripts.ScriptView;
import de.uka.ilkd.key.macros.scripts.ScriptNode;

import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.List;
/*
rule impRight;
rule impRight;
rule notRight;
rule notLeft;
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
            stepOver();
        }
    }

    private void stepOver(){
        view.getTextArea().removeAllLineHighlights();
        view.getPanel().revalidate();
        view.getPanel().repaint();

        List<ScriptNode> state = model.getNextScriptState();
        if(state.size() == 1){
            ScriptNode n = state.get(0);
            int from = n.getFromPos();
            int to = n.getToPos();
            view.getTextArea().highlightLinesatPos(from, to);

        }

    }
}
