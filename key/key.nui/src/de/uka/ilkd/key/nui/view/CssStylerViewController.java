/**
 * 
 */
package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.Map;
import java.util.ResourceBundle;
import java.util.TreeMap;

import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.util.CssFileHandler;
import de.uka.ilkd.key.nui.util.CssRule;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.scene.control.Button;
import javafx.scene.control.ListView;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.stage.Stage;
import javafx.util.Callback;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 *
 */
public class CssStylerViewController extends ViewController {
    private TreeMap<String, CssRule> ruleMap = new TreeMap<>();
    private Stage stage;
    private String selected;
    private CssFileHandler cssFileHandler;

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
        });
    }
    
    private void initializeList(){
        for (CssRule rule : cssFileHandler.getParsedRules()) {
            ruleMap.put(rule.selectorsAsString(), rule);
        }

        ObservableList<String> ruleList = FXCollections
                .observableArrayList(ruleMap.keySet());

        listView.setItems(ruleList);
        listView.setOnMouseClicked(e -> {
            selected = listView.getSelectionModel().getSelectedItem();
            table.setItems(FXCollections.observableArrayList(
                    ((Map) ruleMap.get(selected).getPropertyValuePairs())
                            .entrySet()));
        });
    }

    public void setStage(Stage stage) {
        this.stage = stage;
    }

    @FXML
    private void handleCancel() {
        stage.close();
    }
    
    @FXML
    private void handleApply(){
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
    private void handleReset(){
        cssFileHandler.reset();
        initializeList();
        
        //TODO: Update the List and Table
        
        apply.setDisable(true);
        reset.setDisable(true);
    }

}
