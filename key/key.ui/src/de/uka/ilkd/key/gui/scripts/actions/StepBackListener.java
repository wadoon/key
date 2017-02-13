package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.scripts.DebugModel;
import de.uka.ilkd.key.gui.scripts.ScriptView;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.macros.scripts.ScriptNode;

import java.awt.*;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.List;

/**
 * Controller to handle stepping back in debug mode
 * Created by sarah on 2/10/17.
 */
public class StepBackListener extends KeyAdapter {
    private DebugModel model;
    private ScriptView view;

    public StepBackListener(DebugModel model, ScriptView view) {
        super();
        this.model = model;
        this.view  = view;

    }

    @Override
    public void keyPressed(KeyEvent keyEvent) {
        super.keyPressed(keyEvent);
        if (keyEvent.getKeyCode() == KeyEvent.VK_F4) {
            view.getTextArea().removeAllLineHighlights();
            view.getTextArea().repaint();
            stepBack();
        }
    }

    private void stepBack() {
        view.getTextArea().removeAllLineHighlights();
        view.getTextArea().repaint();
        //this not only return the state but also sets the currentpointer
        model.computePrevState();
        List<ScriptNode> state = model.getCurrentState();
        if (state == null) {
            System.out.println("Previous state is null");
        }

        if(state.size() == 1){
            ScriptNode n = state.get(0);
            int from = n.getFromPos();
            int to = n.getToPos();
            view.getTextArea().highlightLinesatPos(from, to, Color.darkGray);
            view.getTextArea().setCaretPosition(to);
            view.goTo(to);

        }if(state.size() == 0){
            ExceptionDialog.showDialog(view.getMainWindow(), new ScriptException("There is no parsed script to debug."));
        }
        if(state.size()>1){
            for (ScriptNode scriptNode : state) {
                int from = scriptNode.getFromPos();
                int to = scriptNode.getToPos();

                if(model.getCurrentPointerToScript().equals(scriptNode)){
                    view.getTextArea().highlightLinesatPos(from, to, Color.darkGray);
                    view.getTextArea().setCaretPosition(to);
                    view.goTo(to);
                }else{
                    view.getTextArea().highlightLinesatPos(from, to, Color.lightGray);

                }
            }
        }

    }

}
