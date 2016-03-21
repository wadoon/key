package de.uka.ilkd.key.nui;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.gui.notification.events.ProofClosedNotificationEvent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.TaskStartedInfo;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.MiscTools;
import javafx.application.Platform;
import javafx.collections.FXCollections;
import javafx.scene.control.Alert.AlertType;
import javafx.stage.FileChooser;
import javafx.stage.FileChooser.ExtensionFilter;

/**
 * provides functionallity of UserInterface logic for the KeYMediator
 * 
 * @author Benedikt Gross
 * @author Nils Muzzulini
 * @author Victor Schuemmer
 *
 */
public class MediatorUserInterface
        extends AbstractMediatorUserInterfaceControl {

    private StatusManager statusManager;
    private KeYMediator mediator = null;
    private final LinkedList<InteractiveRuleApplicationCompletion> completions = new LinkedList<InteractiveRuleApplicationCompletion>();
    private MainApp mainApp;

    public MediatorUserInterface(StatusManager statusManager, MainApp mainApp) {
        this.statusManager = statusManager;
        this.mainApp = mainApp;
    }

    @Override
    public void completeAndApplyTacletMatch(TacletInstantiationModel[] models,
            Goal goal) {
        
        // models has to be passed via context, as the
        // TacletInstantiationViewController constructor can not be used. There
        // is no need to pass the goal anymore, as the controller can get it
        // directly from the KeYMediator.
        mainApp.getRootLayoutController().getContext().setCurrentModels(models);
        mainApp.openNewWindow("Taclet Instantiation",
                "view/TacletInstantiationView.fxml", true, false,
                FXCollections.observableArrayList(
                        "file:resources/css/tacletInstantiation.css"));
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
        System.out.println("selectProofObligation");
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
        mainApp.getRootLayoutController().addRecentFile(file.getAbsolutePath());
        getProblemLoader(file, null, null, null, getMediator())
                .runAsynchronously();
    }

    @Override
    public void notify(NotificationEvent event) {
        if (event instanceof ProofClosedNotificationEvent) {
            Platform.runLater(() -> {
                mainApp.showAlert("Prove closed", "Proved.", getMediator().getSelectedProof()
                        .getStatistics().toString(), AlertType.INFORMATION);
            });
        }

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
    
    public File saveProof(Proof proof, String fileExtension) {
        FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle("Save current Proof");
        fileChooser.getExtensionFilters().addAll(
                new ExtensionFilter("Proofs, KeY or Java Files", "*.proof", "*.key", "*.java"),
                new ExtensionFilter("All Files", "*.*"));

        String defaultFileName = suggestDefaultFileName(proof, fileExtension);
        fileChooser.setInitialFileName(defaultFileName);
        File file = fileChooser.showSaveDialog(mainApp.getPrimaryStage());
        
        if (file == null) {
            statusManager.setStatus("No file name provided");
            return null;
        }
        
        final String filename = file.getAbsolutePath();
        ProofSaver saver = new ProofSaver(proof, filename, KeYConstants.INTERNAL_VERSION);
        String errorMsg;
        try {
            errorMsg = saver.save();
        }
        catch (IOException e) {
            errorMsg = e.toString();
        }
        if (errorMsg != null) {
            statusManager.setStatus("Saving Proof failed. Error: " + errorMsg);
        }
        else {
            proof.setProofFile(file);
            statusManager.setStatus("Proof saved in: " + file.getAbsolutePath());
        }
        return file;
    }

    private String suggestDefaultFileName(Proof proof, String fileExtension) {
        File selectedFile = null;
        if (proof != null) {
            selectedFile = proof.getProofFile();
        }

        // Suggest default file name if required
        final String defaultName;
        if (selectedFile == null) {
            defaultName = MiscTools.toValidFileName(proof.name().toString()) + fileExtension;
        }
        else if (selectedFile.getName().endsWith(".proof") && fileExtension.equals(".proof")) {
            defaultName = selectedFile.getName();
        }
        else {
            String proofName = proof.name().toString();
            if (proofName.endsWith(".key")) {
                proofName = proofName.substring(0, proofName.lastIndexOf(".key"));
            }
            else if (proofName.endsWith(".proof")) {
                proofName = proofName.substring(0, proofName.lastIndexOf(".proof"));
            }
            System.out.println(proofName);
            defaultName = MiscTools.toValidFileName(proofName) + fileExtension;
        }
        return defaultName;
    }
}
