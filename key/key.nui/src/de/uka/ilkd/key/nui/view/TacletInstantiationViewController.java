package de.uka.ilkd.key.nui.view;

import java.io.StringWriter;
import java.io.Writer;
import java.net.URL;
import java.util.ResourceBundle;

import javax.swing.JScrollPane;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.InstantiationFileHandler;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.util.pp.StringBackend;
import javafx.embed.swing.SwingNode;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.Label;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.TextArea;

public class TacletInstantiationViewController extends ViewController {

    @FXML // fx:id="selectedTacletLabel"
    private Label selectedTacletLabel; // Value injected by FXMLLoader

    @FXML // fx:id="instantiationsTabPane"
    private TabPane instantiationsTabPane; // Value injected by FXMLLoader

    @FXML // fx:id="selectedTaclet"
    private TextArea selectedTaclet; // Value injected by FXMLLoader

    @FXML // fx:id="programVariables"
    private TextArea programVariables; // Value injected by FXMLLoader

    @FXML // fx:id="inputValidation"
    private TextArea inputValidation; // Value injected by FXMLLoader

    private KeYMediator mediator;
    private TacletInstantiationModel[] models;
    private Goal goal;

    private TacletInstantiationDataTable[] dataTable;

    public void init(TacletInstantiationModel[] models, Goal goal) {
        this.models = models;
    }

    private void initProgramVariables() {
        ImmutableList<Named> vars = models[0].programVariables().elements();
        programVariables.setText(vars.size() > 0 ? vars.toString() : "none");

    }

    private void initTaclet() {
        selectedTacletLabel.setText(models[0].taclet().name().toString());

        Taclet taclet = models[0].taclet();
        StringBackend backend = new StringBackend(68);
        StringBuilder tacletSB = new StringBuilder();

        Writer w = new StringWriter();

        // XXX was: SequentViewLogicPrinter. any consequences?
        LogicPrinter printer = new LogicPrinter(new ProgramPrinter(w),
                new NotationInfo(), backend, mediator.getServices(), true);

        printer.printTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS,
                ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                        .getShowWholeTaclet(),
                false);
        tacletSB.append(backend.getString());

        selectedTaclet.setText(tacletSB.toString());
    }

    private void initInputValidation() {
        inputValidation.setText(models[current()].getStatusString());
    }

    @SuppressWarnings("static-access")
    private void initInstantiationsTabPane() {
        for (int i = 0; i < models.length; i++) {
            Tab tab = new Tab("Alt " + i);

            /*
             * TableView table = new TableView(); AnchorPane content = new
             * AnchorPane(table);
             * 
             * content.setBottomAnchor(table, 5.0); content.setTopAnchor(table,
             * 5.0); content.setLeftAnchor(table, 5.0);
             * content.setRightAnchor(table, 5.0);
             * 
             * tab.setContent(content);
             */

            // XXX as a model only delivers a swing table and no actual data,
            // as for now the only possibility is to embed the old JTable.
            // This will however not render properly.
            SwingNode swingNode = new SwingNode();
            dataTable[i] = new TacletInstantiationDataTable(this, i);
            dataTable[i].setRowHeight(48);
            JScrollPane tablePane = new JScrollPane(dataTable[i]);
            // adaptSizes(dataTable[i]);

            if (models[i] != null) {
                dataTable[i].setModel(models[i].tableModel());
                dataTable[i].getColumn(dataTable[i].getColumnName(0))
                        .setHeaderValue("Variable");
                dataTable[i].getColumn(dataTable[i].getColumnName(1))
                        .setHeaderValue("Instantiation");
            }
            swingNode.setContent(dataTable[i]);
            tab.setContent(swingNode);
            instantiationsTabPane.getTabs().add(tab);

            if (!models[i].application().taclet().ifSequent().isEmpty()) {

                // TacletIfSelectionDialog ifSelection = new
                // TacletIfSelectionDialog(models[i], this);
                // dataTable[i].setIfSelectionPanel(ifSelection);
                // tabContent.add(ifSelection);
            }
        }
    }

    private void pushAllInputToModel() {
        pushAllInputToModel(current());
    }

    void pushAllInputToModel(int i) {
        /*
         * if (dataTable[i].hasIfSelectionPanel()) {
         * dataTable[i].getIfSelectionPanel().pushAllInputToModel(); }
         */
        if (dataTable[i].isEditing()) {
            dataTable[i].getCellEditor().stopCellEditing();
        }

    }

    void setStatus(String s) {
        inputValidation.setText(s);
    }

    public int current() {
        int current = instantiationsTabPane.getSelectionModel()
                .getSelectedIndex();
        return (current > -1 ? current : 0);
    }

    public TacletInstantiationModel[] getModels() {
        return models;
    }

    @FXML
    void handleApply(ActionEvent event) {
        try {
            pushAllInputToModel();
            TacletApp app = models[current()].createTacletApp();
            if (app == null) {
                Alert alert = new Alert(AlertType.ERROR);
                alert.setHeaderText("Rule Application Failure");
                alert.setContentText("Could not apply rule");
                return;
            }
            mediator.getUI().getProofControl().applyInteractive(app, goal);
        }
        catch (Exception exc) {
            /*
             * if (exc instanceof SVInstantiationExceptionWithPosition) {
             * errorPositionKnown(exc.getMessage(),
             * ((SVInstantiationExceptionWithPosition) exc).getRow(),
             * ((SVInstantiationExceptionWithPosition) exc).getColumn(),
             * ((SVInstantiationExceptionWithPosition) exc).inIfSequent()); }
             */
            // ExceptionDialog.showDialog(TacletMatchCompletionDialog.this,
            // exc);
            Alert alert = new Alert(AlertType.ERROR);
            alert.setHeaderText("Ooops.");
            alert.setContentText("Something has gone wrong..");
            return;
        }
        InstantiationFileHandler.saveListFor(models[current()]);
        handleClose(event);
    }

    @FXML
    void handleClose(ActionEvent event) {
        mediator.freeModalAccess(this);
        getStage().close();
    }

    @Override
    public void initialize(URL arg0, ResourceBundle arg1) {
        // TODO Auto-generated method stub

    }

    @Override
    public void initializeAfterLoadingFxml() {
        this.mediator = getContext().getKeYMediator();
        mediator.requestModalAccess(this);
        goal = mediator.getSelectedGoal();
        models = getContext().getCurrentModels();

        // XXX see above
        dataTable = new TacletInstantiationDataTable[models.length];

        for (TacletInstantiationModel aModel : models) {
            aModel.prepareUnmatchedInstantiation();
        }

        initProgramVariables();
        initTaclet();
        initInputValidation();
        initInstantiationsTabPane();

    }

    public boolean checkAfterEachInput() {
        // TODO Auto-generated method stub
        return false;
    }
}
