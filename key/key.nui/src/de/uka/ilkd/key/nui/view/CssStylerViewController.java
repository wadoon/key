/**
 * 
 */
package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.util.CssFileHandler;
import de.uka.ilkd.key.nui.util.CssRule;
import de.uka.ilkd.key.nui.util.PreviewPrinter;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar.ButtonData;
import javafx.scene.control.ButtonType;
import javafx.scene.control.ListView;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.scene.web.WebView;
import javafx.stage.Stage;
import javafx.util.Callback;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 *
 */
public class CssStylerViewController extends ViewController {
    private LinkedHashMap<String, CssRule> ruleMap = new LinkedHashMap<>();
    private Stage stage;
    private String selected;
    private CssFileHandler cssFileHandler;
    private PreviewPrinter previewPrinter = new PreviewPrinter();

    @FXML
    private ListView<String> listView;
    @FXML
    private TableColumn<Map.Entry<String, String>, String> propertyColumn;
    @FXML
    private TableColumn<Map.Entry<String, String>, String> valueColumn;
    @FXML
    private TableView<Map<String, String>> table;
    @FXML
    private Button apply;
    @FXML
    private Button reset;
    @FXML
    private WebView previewWeb;

    @Override
    public void initialize(URL location, ResourceBundle resources) {

    }

    @Override
    public void initializeAfterLoadingFxml() {
        cssFileHandler = getContext().getCssFileHandler();

        initializeList();

        propertyColumn.setCellValueFactory(
                new Callback<TableColumn.CellDataFeatures<Map.Entry<String, String>, String>, ObservableValue<String>>() {

                    @Override
                    public ObservableValue<String> call(
                            TableColumn.CellDataFeatures<Map.Entry<String, String>, String> p) {
                        // this callback returns property for just one cell, you
                        // can't use a loop here
                        // for first column we use key
                        return new SimpleStringProperty(p.getValue().getKey());
                    }
                });
        valueColumn.setCellFactory(TextFieldTableCell.forTableColumn());
        valueColumn.setCellValueFactory(
                new Callback<TableColumn.CellDataFeatures<Map.Entry<String, String>, String>, ObservableValue<String>>() {

                    @Override
                    public ObservableValue<String> call(
                            TableColumn.CellDataFeatures<Map.Entry<String, String>, String> p) {
                        // this callback returns property for just one cell, you
                        // can't use a loop here
                        // for first column we use key
                        return new SimpleStringProperty(
                                p.getValue().getValue());
                    }
                });
        valueColumn.setOnEditCommit(e -> {
            ruleMap.get(selected).getPropertyValuePairs()
                    .put(e.getRowValue().getKey(), e.getNewValue());
            apply.setDisable(false);
            reset.setDisable(false);
            this.updatePreview();
        });
    }

    private void initializeList() {
        for (CssRule rule : cssFileHandler.getParsedRules()) {
            ruleMap.put(rule.selectorsAsString(), rule);
        }

        ObservableList<String> ruleList = FXCollections
                .observableArrayList(ruleMap.keySet());

        listView.setItems(ruleList);
        listView.getSelectionModel().selectedItemProperty().addListener(e -> {
            selected = listView.getSelectionModel().getSelectedItem();
            updateTable();
            updatePreview();
        });
    }

    private void updateTable() {
        table.setItems(FXCollections.observableArrayList(
                ((Map) ruleMap.get(selected).getPropertyValuePairs())
                        .entrySet()));
    }

    private void updatePreview() {
        previewWeb.getEngine().loadContent(previewPrinter
                .printPreview(cssFileHandler.parsedRulestoString(), selected));
    }

    public void setStage(Stage stage) {
        this.stage = stage;
    }

    @FXML
    private void handleCancel() {
        if (apply.disabledProperty().get() == false) {
            Alert alert = new Alert(AlertType.CONFIRMATION);
            alert.setTitle("Confirm Exit");
            alert.setHeaderText("Do you want to save your changes?");
            alert.setContentText("Unsaved changes will be lost upon exit");

            ButtonType saveExit = new ButtonType("Save and Exit");
            ButtonType resetExit = new ButtonType("Exit without Saving");
            ButtonType cancel = new ButtonType("Cancel",
                    ButtonData.CANCEL_CLOSE);

            alert.getButtonTypes().setAll(saveExit, resetExit, cancel);

            Optional<ButtonType> result = alert.showAndWait();
            if (result.get() == saveExit) {
                handleApply();
                alert.close();
            }
            else if (result.get() == resetExit) {
                handleReset();
                alert.close();
            }
            else {
                alert.close();
                return;
            }
        }
        stage.close();
    }

    @FXML
    private void handleApply() {
        try {
            cssFileHandler.writeCssFile();
        }
        catch (Exception e) {
            System.err.println("Could not write CSS File");
        }

        apply.setDisable(true);
        reset.setDisable(true);
    }

    @FXML
    private void handleReset() {
        cssFileHandler.reset();
        initializeList();

        updateTable();
        updatePreview();
        
        apply.setDisable(true);
        reset.setDisable(true);
    }

}
