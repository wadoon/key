package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.scripts.DebugModel;
import de.uka.ilkd.key.gui.scripts.ScriptView;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.macros.scripts.ScriptNode;

import java.awt.*;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.List;

/**
 * Created by sarah on 2/10/17.
 */
public class SelectDebugFocusAction extends KeyAdapter {

    private DebugModel model;
    private ScriptView view;

    public SelectDebugFocusAction(DebugModel model, ScriptView view) {
        this.model = model;
        this.view = view;
    }

    @Override
    public void keyPressed(KeyEvent keyEvent) {
        super.keyPressed(keyEvent);
        if (keyEvent.getKeyCode() == KeyEvent.VK_F2) {
            ScriptNode currentPointer = model.getCurrentPointerToScript();
            List<ScriptNode> currentState = model.getCurrentState();
            if(currentState.size()> 1){
                boolean foundChild = false;
                ScriptNode firstChild = currentState.get(0);

                for (ScriptNode scriptNode : currentState) {

                    if(foundChild){
                        try {
                            model.setCurrentPointerToScript(scriptNode);
                        } catch (ScriptException e) {
                            e.printStackTrace();
                        }
                        break;
                    }
                    if(scriptNode.equals(currentPointer) && !scriptNode.equals(currentState.get(currentState.size()-1))){
                        foundChild = true;
                    }
                }
                if(!foundChild){
                    try {
                        model.setCurrentPointerToScript(firstChild);
                    } catch (ScriptException e) {
                        e.printStackTrace();
                    }
                }
                changeFocus();
            }else{
                keyEvent.consume();
            }
        }
    }

    public void changeFocus() {
        view.getTextArea().removeAllLineHighlights();
        for (ScriptNode scriptNode : model.getCurrentState()) {
            int from = scriptNode.getFromPos();
            int to = scriptNode.getToPos();

            if (model.getCurrentPointerToScript().equals(scriptNode)) {
                view.getTextArea().highlightLinesatPos(from, to, Color.darkGray);
                view.getTextArea().setCaretPosition(to);
                view.goTo(to);
            } else {
                view.getTextArea().highlightLinesatPos(from, to, Color.lightGray);

            }
        }


    }
}
