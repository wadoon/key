package de.uka.ilkd.key.nui.view;

import java.io.StringWriter;
import java.io.Writer;
import java.util.function.Function;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.InstantiationFileHandler;
import de.uka.ilkd.key.control.instantiation_model.TacletFindModel;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.InstantiationProposerCollection;
import de.uka.ilkd.key.proof.VariableNameProposer;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.util.pp.StringBackend;
import javafx.application.Platform;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.css.PseudoClass;
import javafx.event.ActionEvent;
import javafx.event.Event;
import javafx.fxml.FXML;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.Label;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.TableCell;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableRow;
import javafx.scene.control.TableView;
import javafx.scene.control.TextArea;
import javafx.scene.layout.AnchorPane;
import javafx.util.Callback;

/**
 * A view for instantiation of taclets.
 * 
 * @author Victor Schuemmer
 */
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

    private InstantiationProposerCollection instantiationProposers;

    @Override
    public void initializeAfterLoadingFxml() {
        this.mediator = getContext().getKeYMediator();
        mediator.requestModalAccess(this);
        goal = mediator.getSelectedGoal();
        models = getContext().getCurrentModels();

        for (TacletInstantiationModel aModel : models) {
            aModel.prepareUnmatchedInstantiation();
        }

        instantiationProposers = new InstantiationProposerCollection();
        instantiationProposers.add(mediator.getServices().getVariableNamer());
        instantiationProposers.add(VariableNameProposer.DEFAULT);

        showProgramVariables();
        showTacletDescription();
        showInstantiationsTabPane();
        setStatus(models[current()].getStatusString());

        getStage().getScene().getWindow().setOnCloseRequest(this::handleClose);
    }

    /**
     * Shows program variables in the corresponding area.
     */
    private void showProgramVariables() {
        ImmutableList<Named> vars = models[0].programVariables().elements();
        programVariables.setText(vars.size() > 0 ? vars.toString() : "none");

    }

    /**
     * Shows the description of the selected taclet in the corresponding area.
     */
    private void showTacletDescription() {
        selectedTacletLabel.setText(models[0].taclet().name().toString());

        Taclet taclet = models[0].taclet();
        StringBackend backend = new StringBackend(68);
        StringBuilder tacletSB = new StringBuilder();

        Writer w = new StringWriter();

        // XXX Formerly SequentViewLogicPrinter was used here. Any consequences?
        LogicPrinter printer = new LogicPrinter(new ProgramPrinter(w),
                new NotationInfo(), backend, mediator.getServices(), true);

        printer.printTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS,
                ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                        .getShowWholeTaclet(),
                false);
        tacletSB.append(backend.getString());

        selectedTaclet.setText(tacletSB.toString());
    }

    /**
     * Shows a tab for every model with the possibility to complete them.
     */
    @SuppressWarnings({ "static-access", "unchecked" })
    private void showInstantiationsTabPane() {
        for (int i = 0; i < models.length; i++) {
            // Create new tab for every alternative.
            Tab tab = new Tab("Alt " + i);
            TableView<TacletInstantiationRowModel> table = new TableView<TacletInstantiationRowModel>();
            AnchorPane content = new AnchorPane(table);
            content.setBottomAnchor(table, 5.0);
            content.setTopAnchor(table, 5.0);
            content.setLeftAnchor(table, 5.0);
            content.setRightAnchor(table, 5.0);
            tab.setContent(content);
            instantiationsTabPane.getTabs().add(tab);

            // Build a table model from the swing table model returned by the
            // TacletInstantiationModel.
            ObservableList<TacletInstantiationRowModel> tableModel = FXCollections
                    .observableArrayList();
            TacletFindModel tfm = models[i].tableModel();
            for (int j = 0; j < tfm.getRowCount(); j++) {
                tableModel.add(new TacletInstantiationRowModel(
                        (SchemaVariable) tfm.getValueAt(j, 0),
                        (String) tfm.getValueAt(j, 1), j,
                        tfm.isCellEditable(j, 1)));
            }

            TableColumn<TacletInstantiationRowModel, SchemaVariable> variableColumn = createCol(
                    "Variable", TacletInstantiationRowModel::variableProperty);
            TableColumn<TacletInstantiationRowModel, String> instantiationColumn = createCol(
                    "Instantiation",
                    TacletInstantiationRowModel::instantiationProperty);
            int modelNr = i;

            // Push edits back to swing table model.
            instantiationColumn.setOnEditCommit(evt -> {
                TacletInstantiationRowModel rowModel = evt.getRowValue();
                rowModel.setInstantiation(evt.getNewValue());
                if (modelNr == current()) {
                    models[modelNr].tableModel().setValueAt(
                            rowModel.getInstantiation(),
                            evt.getRowValue().getRowNumber(), 1);
                    setStatus(models[modelNr].getStatusString());
                }
            });

            Callback<TableColumn<TacletInstantiationRowModel, String>, TableCell<TacletInstantiationRowModel, String>> defaultTextFieldCellFactory = TextAreaTableCell
                    .<TacletInstantiationRowModel> forTableColumn();

            // Pseudo class for editable table cells.
            PseudoClass editableCssClass = PseudoClass
                    .getPseudoClass("editable");
            // Pseudo class for rows that do not allow editing.
            PseudoClass completedCssClass = PseudoClass
                    .getPseudoClass("completed");

            // Cell factory which makes the appropriate cells editable
            instantiationColumn.setCellFactory(cellData -> {
                TableCell<TacletInstantiationRowModel, String> cell = defaultTextFieldCellFactory
                        .call(cellData);
                cell.itemProperty().addListener((obs, oldValue, newValue) -> {
                    TableRow<TacletInstantiationRowModel> row = cell
                            .getTableRow();
                    if (row == null) {
                        cell.setEditable(false);
                    }
                    else {
                        TacletInstantiationRowModel rowModel = row.getItem();
                        if (rowModel == null) {
                            cell.setEditable(false);
                        }
                        else {
                            boolean editable = rowModel.isEditable();
                            cell.setEditable(editable);
                            row.setDisable(!editable);
                            cell.pseudoClassStateChanged(editableCssClass,
                                    editable);
                            row.pseudoClassStateChanged(completedCssClass,
                                    !editable);
                        }
                    }
                });
                return cell;
            });

            // Show data in table.
            table.setEditable(true);
            table.getColumns().addAll(variableColumn, instantiationColumn);
            table.setColumnResizePolicy(TableView.CONSTRAINED_RESIZE_POLICY);
            table.setItems(tableModel);

            // when the tab is changed, instantly select the first editable cell
            // and put it in selection mode
            tab.setOnSelectionChanged(event -> {
                focusFirstEditable(table, instantiationColumn);
            });

            // select first tab for instant editing
            if (i == 0)
                focusFirstEditable(table, instantiationColumn);

            if (!models[i].application().taclet().ifSequent().isEmpty()) {
                // TODO implement TacletIfSelectionDialog

                // TacletIfSelectionDialog ifSelection = new
                // TacletIfSelectionDialog(models[i], this);
                // dataTable[i].setIfSelectionPanel(ifSelection);
                // tabContent.add(ifSelection);
            }
        }
    }

    /**
     * Focuses the first editable row in the given table and switches the
     * editable cell to edit state.
     * 
     * @param table
     *            the table
     * @param col
     *            the column with the editable cells
     */
    private void focusFirstEditable(
            TableView<TacletInstantiationRowModel> table,
            TableColumn<TacletInstantiationRowModel, ?> col) {
        Platform.runLater(() -> {
            for (TacletInstantiationRowModel m : table.getItems()) {
                if (m.isEditable() && table.getEditingCell() == null) {
                    table.requestFocus();
                    table.edit(m.getRowNumber(), col);
                    table.getSelectionModel().select(m.getRowNumber());
                    table.getFocusModel().focus(m.getRowNumber());
                    break;
                }
            }
        });
    }

    /**
     * Creates a new column for the table
     * 
     * @param title
     *            the title of the column
     * @param property
     *            function of the model that provides the data
     * @return the column
     */
    private <S, T> TableColumn<S, T> createCol(String title,
            Function<S, ObservableValue<T>> property) {
        TableColumn<S, T> col = new TableColumn<>(title);
        col.setCellValueFactory(
                cellData -> property.apply(cellData.getValue()));
        return col;
    }

    /**
     * Sets the text of the input validation text area.
     */
    private void setStatus(String s) {
        inputValidation.setText(s);
    }

    /**
     * @return the currently selected model
     */
    private int current() {
        int current = instantiationsTabPane.getSelectionModel()
                .getSelectedIndex();
        return (current > -1 ? current : 0);
    }

    /**
     * Applies the rule.
     */
    @FXML
    private void handleApply(ActionEvent event) {
        try {
            TacletApp app = models[current()].createTacletApp();
            if (app == null) {
                getMainApp().showAlert("Error", "Rule Application Failure",
                        "Could not apply rule.", AlertType.ERROR);
                return;
            }
            mediator.getUI().getProofControl().applyInteractive(app, goal);
        }
        catch (Exception exc) {
            getMainApp().showAlert("Error", "Rule Application Failure",
                    exc.toString(), AlertType.ERROR);
            return;
        }
        InstantiationFileHandler.saveListFor(models[current()]);
        handleClose(event);
    }

    /**
     * Frees modal access and closes the stage.
     */
    @FXML
    private void handleClose(Event event) {
        mediator.freeModalAccess(this);
        getStage().close();
    }
}
