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
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.TaskStartedInfo;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;

/**
 * provides functionallity of UserInterface logic for the KeYMediator
 * @author Benedikt Gross
 *
 */
public class MediatorUserInterface
        extends AbstractMediatorUserInterfaceControl {

    private IStatusManager statusManager;
    private KeYMediator mediator = null;
    private final LinkedList<InteractiveRuleApplicationCompletion> completions = new LinkedList<InteractiveRuleApplicationCompletion>();

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
            return AbstractProofControl.completeBuiltInRuleAppByDefault(app,
                    goal, forced);
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
        mediator.stopInterface(true);
    }

    @Override
    public void progressStopped(Object sender) {
        mediator.startInterface(true);
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

    public void setMediator(KeYMediator value) {
        mediator = value;
    }

    @Override
    public void loadProblem(File file) {
        getProblemLoader(file, null, null, null, getMediator())
                .runAsynchronously();
    }

    @Override
    public void notify(NotificationEvent event) {
        // TODO Auto-generated method stub

    }

    @Override
    public void taskProgress(int position) {
        super.taskProgress(position);
        // mainWindow.getStatusLine().setProgress(position);

    }

    @Override
    public void taskStarted(TaskStartedInfo info) {
        super.taskStarted(info);
        // mainWindow.setStatusLine(info.getMessage(), info.getSize());
    }

    @Override
    public void loadingStarted(AbstractProblemLoader loader) {
        getMediator().stopInterface(true);
        super.loadingStarted(loader);
    }

    // TODO: remove unnecessary code - just copied from
    // WindowUserInterfaceController
    @Override
    public void loadingFinished(AbstractProblemLoader loader,
            LoadedPOContainer poContainer, ProofAggregate proofList,
            ReplayResult result) throws ProblemLoaderException {
        super.loadingFinished(loader, poContainer, proofList, result);
        if (proofList != null) {
            getMediator().setProof(loader.getProof());
            if (result != null) {
                if ("".equals(result.getStatus())) {
                    this.resetStatus(this);
                }
                else {
                    this.reportStatus(this, result.getStatus());
                }
                getMediator().getSelectionModel()
                        .setSelectedNode(result.getNode());
                if (result.hasErrors()) {
                    throw new ProblemLoaderException(loader,
                            "Proof could only be loaded partially.\n"
                                    + "In summary "
                                    + result.getErrorList().size()
                                    + " not loadable rule application(s) have been detected.\n"
                                    + "The first one:\n"
                                    + result.getErrorList().get(0).getMessage(),
                            result.getErrorList().get(0));
                }
            }
            else {
                // should never happen as replay always returns a result object
                // TODO (DS): Why is it then there? If this happens, we will
                // get\\
                // a NullPointerException just a line below...
                getMediator().getSelectionModel()
                        .setSelectedNode(loader.getProof().root());
            }

        }
        getMediator().resetNrGoalsClosedByHeuristics();
        if (poContainer != null && poContainer
                .getProofOblInput() instanceof KeYUserProblemFile) {
            ((KeYUserProblemFile) poContainer.getProofOblInput()).close();
        }
    }
}
