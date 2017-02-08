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

    public static final String name = "Step Mode";
    public static final String start = "Start Step Mode";
    public static final String stop = "Stop Step Mode";

    private StepOverListener stepOverListener;

    public StepModeAction(JButton stepButton, ScriptView scriptView, ActualScript currentScript) {
        super(name, scriptView, currentScript);
        this.stepMode = stepButton;

    }

    @Override
    public void actionPerformed(ActionEvent actionEvent) {
        if(stepMode.getText().equals(start)) {
            if (getActualScript().getCurrentRoot() != null) {
                startStepMode(super.getActualScript(), super.getActualScript().getAssociatedProof());
                stepMode.setText(stop);
            }else{
                ExceptionDialog.showDialog(getView().getMainWindow(), new ScriptException("There is no script to step through"));

            }

        }else{
            stopStepMode(super.getActualScript(), super.getActualScript().getAssociatedProof());
            stepMode.setText(start);
        }
    }

    private void stopStepMode(ActualScript actualScript, Proof associatedProof) {
        super.getView().getTextArea().removeKeyListener(stepOverListener);
        super.getView().enableReset();
        super.getView().getTextArea().removeAllLineHighlights();
        super.getView().getTextArea().setCurrentLineHighlightColor(new Color(1f, 1f, 0.5f, 0.8f));
        super.getView().getTextArea().setHighlightCurrentLine(true);
        super.getView().getTextArea().repaint();
    }

    private void startStepMode(ActualScript actualScript, Proof associatedProof){

        super.getView().disableReset();

        DebugModel model;
        int pos = super.getView().getTextArea().getCaretPosition();
        getView().getTextArea().setCaretPosition(pos);

        ScriptNode currNode = super.getView().getNodeAtPos(actualScript.getCurrentRoot(), pos);

        if(currNode.equals(actualScript.getCurrentRoot())) {
            model = new DebugModel(actualScript, associatedProof);
        }else{
            model = new DebugModel(actualScript, associatedProof, currNode, currNode.getProofNode());
        }
        stepOverListener = new StepOverListener(model, super.getView());

        super.getView().getTextArea().setCurrentLineHighlightColor(Color.lightGray);
        super.getView().getTextArea().setHighlightCurrentLine(true);
        super.getView().getTextArea().repaint();

        super.getView().getTextArea().addKeyListener(stepOverListener);

    }


}
