package de.uka.ilkd.key.nui;

import java.io.File;
import java.util.LinkedList;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.nui.util.IStatusManager;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;

public class MediatorUserInterface
        extends AbstractMediatorUserInterfaceControl {

    private IStatusManager statusManager;
    private KeYMediator mediator;
    private final LinkedList<InteractiveRuleApplicationCompletion> completions =
            new LinkedList<InteractiveRuleApplicationCompletion>();

    public MediatorUserInterface(IStatusManager statusManager) {
        this.statusManager = statusManager;
    }

    @Override
    public void completeAndApplyTacletMatch(TacletInstantiationModel[] models,
            Goal goal) {
        // TODO Auto-generated method stub

    }

    @Override
    public IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app,
            Goal goal, boolean forced) {
        if (getMediator().isInAutoMode()) {
            return AbstractProofControl.completeBuiltInRuleAppByDefault(app, goal, forced);
        }
        IBuiltInRuleApp result = app;
        for (InteractiveRuleApplicationCompletion compl : completions) {
            if (compl.canComplete(app)) {
                result = compl.complete(app, goal, forced);
                break;
            }
        }
        return (result != null && result.complete()) ? result : null;
    }

    @Override
    public boolean selectProofObligation(InitConfig initConfig) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public void reportWarnings(ImmutableSet<PositionedString> warnings) {
        // TODO Auto-generated method stub

    }

    @Override
    public void progressStarted(Object sender) {
        // TODO Auto-generated method stub

    }

    @Override
    public void progressStopped(Object sender) {
        // TODO Auto-generated method stub

    }

    @Override
    public void reportStatus(Object sender, String status, int progress) {
        statusManager.setStatus(status + " " + progress);
    }

    @Override
    public void reportStatus(Object sender, String status) {
        statusManager.setStatus(status);
    }

    @Override
    public void resetStatus(Object sender) {
        statusManager.clearStatus();
    }

    @Override
    public void reportException(Object sender, ProofOblInput input,
            Exception e) {
        throw new RuntimeException(e);
    }

    @Override
    public void setProgress(int progress) {
        // TODO Auto-generated method stub

    }

    @Override
    public void setMaximum(int maximum) {
        // TODO Auto-generated method stub

    }

    @Override
    public void openExamples() {
        // TODO Auto-generated method stub

    }
    
    @Override
    public KeYMediator getMediator() {
        return mediator;
    }
    
    public void setMediator(KeYMediator value){
        mediator = value;
    }

    @Override
    public void loadProblem(File file) {
        getProblemLoader(file, null, null, null, getMediator()).runAsynchronously();
    }

    @Override
    public void notify(NotificationEvent event) {
        // TODO Auto-generated method stub

    }

}
