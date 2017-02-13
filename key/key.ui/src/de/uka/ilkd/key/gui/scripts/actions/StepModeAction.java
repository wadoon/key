package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.scripts.ActualScript;
import de.uka.ilkd.key.gui.scripts.DebugModel;
import de.uka.ilkd.key.gui.scripts.ScriptTextArea;
import de.uka.ilkd.key.gui.scripts.ScriptView;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.macros.scripts.ScriptNode;
import de.uka.ilkd.key.proof.Proof;

import java.awt.*;
import java.awt.event.ActionEvent;

/**
 * Controller for managing the debugmodes.
 * Created by sarah on 2/6/17.
 */
public class StepModeAction extends AbstractScriptAction {



    public static final String START = "Start Step Mode";
    public static final String STOP = "Stop Step Mode";

    /**
     * Controller to step Forward
     */
    private StepOverListener stepOverListener;

    /**
     *  Controller to step backwards through script
     */
    private StepBackListener stepBackListener;

    /**
     * Controller to step into a macro
     */
    //private StepIntoListsner stepintoListsner;

    /**
     * Controller to return from step into
     */
    //private StepReturnListener stepReturnListsner;

    private SelectDebugFocusAction selectDebugFocus;
    public StepModeAction(ScriptView scriptView) {
        super(START, scriptView);
    }

    @Override
    public void actionPerformed(ActionEvent actionEvent) {
        if(getValue(NAME).equals(START)) {
            if (getView().getCurrentScript().getCurrentRoot() != null) {
                startStepMode(getView().getCurrentScript(), getView().getCurrentScript().getAssociatedProof());
                putValue(NAME, STOP);
            }else{
                ExceptionDialog.showDialog(getView().getMainWindow(), new ScriptException("There is no script to step through"));

            }
        }else{
            stopStepMode(getView().getCurrentScript(), getView().getCurrentScript().getAssociatedProof());
            putValue(NAME, START);

        }
    }

    /**
     * Stop stepping through the script
     * @param actualScript
     * @param associatedProof
     */
    private void stopStepMode(ActualScript actualScript, Proof associatedProof) {
        ScriptView view = super.getView();
        view.getTextArea().setFocusTraversalKeysEnabled(true);
        view.getTextArea().removeKeyListener(stepOverListener);
        view.getTextArea().removeKeyListener(stepBackListener);
        view.enableReset();
        view.getTextArea().removeAllLineHighlights();
        view.getTextArea().repaint();
    }

    /**
     * Start stepping through script
     * @param actualScript
     * @param associatedProof
     */
    private void startStepMode(ActualScript actualScript, Proof associatedProof){
        DebugModel model;


        ScriptView view = super.getView();
        view.disableReset();

        ScriptTextArea textArea = view.getTextArea();
        int pos = textArea.getCaretPosition();


        ScriptNode currNode = view.getNodeAtPos(actualScript.getCurrentRoot(), pos);

        if(currNode.equals(actualScript.getCurrentRoot())) {
            model = new DebugModel(actualScript, associatedProof);
        }else{
            model = new DebugModel(actualScript, associatedProof, currNode, currNode.getProofNode());
        }
        textArea.setFocusTraversalKeysEnabled(false);
        selectDebugFocus = new SelectDebugFocusAction(model, view);
        stepOverListener = new StepOverListener(model, view);
        stepBackListener = new StepBackListener(model, view);
        textArea.removeAllLineHighlights();
        //textArea.setCurrentLineHighlightColor(Color.lightGray);
        textArea.highlightLine(textArea.getCaretLineNumber(), Color.darkGray);
        textArea.repaint();
        textArea.setCaretPosition(pos);
        textArea.addKeyListener(stepOverListener);
        textArea.addKeyListener(stepBackListener);

    }


}
