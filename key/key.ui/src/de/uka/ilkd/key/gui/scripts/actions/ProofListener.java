package de.uka.ilkd.key.gui.scripts.actions;


import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.scripts.ActualScript;
import de.uka.ilkd.key.gui.scripts.ScriptView;
import de.uka.ilkd.key.proof.Proof;

import java.util.List;

/**
 * Created by sarah on 2/9/17.
 */
public class ProofListener implements KeYSelectionListener{

    private ScriptView view;

    public ProofListener(ScriptView view){
        this.view = view;
    }


    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {

    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {

      /*  String text = view.getTextArea().getText();
        System.out.println("Old Script: "+text);
        ActualScript script= view.getCurrentScript();
        List<ActualScript> activeScripts = view.getActiveScripts();
        if(!script.getTextReprOfScript().equals(text)) {
            view.getCurrentScript().setTextReprOfScript(text);
        }
        if(!activeScripts.contains(script)){
            view.getActiveScripts().add(script);
        }*/
        view.setCurrentScript(null);
        List<ActualScript> activeScripts = view.getActiveScripts();
        for (ActualScript activeScript : activeScripts) {
            //is null at the beginning
            Proof activeProof = activeScript.getAssociatedProof();
            if (activeProof != null) {

                if (activeProof.equals(e.getSource().getSelectedProof())) {
                    view.setCurrentScript(activeScript);
                    break;
                }
            }

        }
        if(view.getCurrentScript() == null) {
            ActualScript s = new ActualScript(view.getMediator());
            view.getActiveScripts().add(s);
            view.setCurrentScript(s);
        }
        view.getTextArea().loadCurrentScriptToTextarea(view);
    }


}
