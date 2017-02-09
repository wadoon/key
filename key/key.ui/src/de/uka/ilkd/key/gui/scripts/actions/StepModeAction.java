package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.scripts.ActualScript;
import de.uka.ilkd.key.gui.scripts.DebugModel;
import de.uka.ilkd.key.gui.scripts.ScriptView;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.macros.scripts.ScriptNode;
import de.uka.ilkd.key.proof.Proof;

import javax.swing.*;

import java.awt.*;
import java.awt.event.ActionEvent;

/**
 * Created by sarah on 2/6/17.
 */
public class StepModeAction extends AbstractScriptAction {
    private JButton stepMode;


    public static final String START = "Start Step Mode";
    public static final String STOP = "Stop Step Mode";

    private StepOverListener stepOverListener;

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

    private void stopStepMode(ActualScript actualScript, Proof associatedProof) {
        ScriptView view = super.getView();
        view.getTextArea().removeKeyListener(stepOverListener);
        view.enableReset();
        view.getTextArea().removeAllLineHighlights();
        view.getTextArea().setCurrentLineHighlightColor(new Color(1f, 1f, 0.5f, 0.8f));
        view.getTextArea().setHighlightCurrentLine(true);
        view.getTextArea().repaint();
    }

    private void startStepMode(ActualScript actualScript, Proof associatedProof){

        ScriptView view = super.getView();
        view.disableReset();

        DebugModel model;
        int pos = view.getTextArea().getCaretPosition();


        ScriptNode currNode = view.getNodeAtPos(actualScript.getCurrentRoot(), pos);

        if(currNode.equals(actualScript.getCurrentRoot())) {
            model = new DebugModel(actualScript, associatedProof);
        }else{
            model = new DebugModel(actualScript, associatedProof, currNode, currNode.getProofNode());
        }
        stepOverListener = new StepOverListener(model, view);
        view.getTextArea().removeAllLineHighlights();
        view.getTextArea().setCurrentLineHighlightColor(Color.lightGray);
        view.getTextArea().highlightLine(view.getTextArea().getCaretLineNumber());
        view.getTextArea().repaint();
        view.getTextArea().setCaretPosition(pos);
        view.getTextArea().addKeyListener(stepOverListener);

    }


}
