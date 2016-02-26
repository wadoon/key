/**
 * 
 */
package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.util.CssFileHandler;
import de.uka.ilkd.key.nui.util.CssRule;
import de.uka.ilkd.key.nui.util.NUIConstants;
import de.uka.ilkd.key.nui.util.PreviewPrinter;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.scene.Node;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar.ButtonData;
import javafx.scene.control.ButtonType;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ColorPicker;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;
import javafx.scene.control.ListView;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.TextField;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;
import javafx.scene.paint.Color;
import javafx.scene.web.WebView;
import javafx.util.Callback;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 *
 */
public class CssStylerViewController extends ViewController {
    private LinkedHashMap<String, CssRule> ruleMap = new LinkedHashMap<>();
    private String selected;
    private CssFileHandler cssFileHandler;
    private PreviewPrinter previewPrinter = new PreviewPrinter();
    private HashMap<String, String> masterRules;

    private ObservableList<String> fontWeight = FXCollections
            .observableArrayList("normal", "bold");
    private ObservableList<String> fontStyle = FXCollections
            .observableArrayList("normal", "italic");
    private ObservableList<String> fontFamily = FXCollections
            .observableArrayList("Arial", "Liberation Mono", "Courier New",
                    "Comic Sans", "Times New Roman");

    @FXML
    private ListView<String> listView;
    @FXML
    private Button apply;
    @FXML
    private Button reset;
    @FXML
    private Button resetDefault;
    @FXML
    private WebView previewWeb;
    @FXML
    private GridPane propValGrid;

    @Override
    public void initialize(URL location, ResourceBundle resources) {

    }

    @Override
    public void initializeAfterLoadingFxml() {
        cssFileHandler = getContext().getCssFileHandler();

        initializeList();
    }

    private void initializeList() {
        for (CssRule rule : cssFileHandler.getParsedRules()) {
            String ruleDescription = NUIConstants.getClassDescriptionMap()
                    .get(rule.selectorsAsString());
            
            if (ruleDescription != null){
                ruleMap.put(ruleDescription, rule);
            }else{
                ruleMap.put(rule.selectorsAsString(), rule);
            }

            if (rule.selectorsAsString().equals("pre")) {
                masterRules = rule.getPropertyValuePairs();
            }
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
        if (selected == null) {
            return;
        }

        propValGrid.getChildren().clear();

        HashMap<String, String> propertyValuePairMap = ruleMap.get(selected)
                .getPropertyValuePairs();
        int i = 0;
        for (String property : propertyValuePairMap.keySet()) {
            String value = propertyValuePairMap.get(property);
            String propertyLabel;
            Node valueNode;
            boolean inherited = false;

            if (value.equals("inherit")) {
                value = masterRules.get(property);
                inherited = true;
            }

            switch (property) {
            case "background-color":
                propertyLabel = "Background Color:";
                valueNode = new ColorPicker(convertToColor(value));
                ((ColorPicker) valueNode).setOnAction(event -> {
                    Color c = ((ColorPicker) valueNode).getValue();

                    propertyValuePairMap.put(property,
                            String.format("#%02X%02X%02X",
                                    (int) (c.getRed() * 255),
                                    (int) (c.getGreen() * 255),
                                    (int) (c.getBlue() * 255)));
                    updatePreview();
                    apply.setDisable(false);
                    reset.setDisable(false);
                });
                break;
            case "color":
                propertyLabel = "Font Color:";
                valueNode = new ColorPicker(convertToColor(value));
                ((ColorPicker) valueNode).setOnAction(event -> {
                    Color c = ((ColorPicker) valueNode).getValue();

                    propertyValuePairMap.put(property,
                            String.format("#%02X%02X%02X",
                                    (int) (c.getRed() * 255),
                                    (int) (c.getGreen() * 255),
                                    (int) (c.getBlue() * 255)));
                    updatePreview();
                    apply.setDisable(false);
                    reset.setDisable(false);
                });
                break;
            case "font-weight":
                propertyLabel = "Boldness:";
                valueNode = new ComboBox<>(fontWeight);
                ((ComboBox<String>) valueNode).setValue(value);
                ((ComboBox<String>) valueNode).setOnAction(event -> {
                    propertyValuePairMap.put(property,
                            ((ComboBox<String>) valueNode).getValue());
                    updatePreview();
                    apply.setDisable(false);
                    reset.setDisable(false);
                });
                break;
            case "font-size":
                propertyLabel = "Font Size in px:";
                valueNode = new TextField(
                        value.substring(0, value.length() - 2));
                ((TextField) valueNode).setOnAction(event -> {
                    propertyValuePairMap.put(property,
                            ((TextField) valueNode).getText());
                    updatePreview();
                    apply.setDisable(false);
                    reset.setDisable(false);
                });
                break;
            case "font-family":
                propertyLabel = "Font:";
                valueNode = new ComboBox<>(fontFamily);
                ((ComboBox<String>) valueNode).setValue(value);
                ((ComboBox<String>) valueNode).setOnAction(event -> {
                    propertyValuePairMap.put(property,
                            ((ComboBox<String>) valueNode).getValue());
                    updatePreview();
                    apply.setDisable(false);
                    reset.setDisable(false);
                });
                break;
            case "font-style":
                propertyLabel = "Italics:";
                valueNode = new ComboBox<>(fontStyle);
                ((ComboBox<String>) valueNode).setValue(value);
                ((ComboBox<String>) valueNode).setOnAction(event -> {
                    propertyValuePairMap.put(property,
                            ((ComboBox<String>) valueNode).getValue());
                    updatePreview();
                    apply.setDisable(false);
                    reset.setDisable(false);
                });
                break;
            case "display":
                propertyLabel = "Do not edit this rule!";
                valueNode = new Label();
                break;
            default:
                propertyLabel = property;
                valueNode = new TextField(value);
                ((TextField) valueNode).setOnAction(event -> {
                    propertyValuePairMap.put(property,
                            ((TextField) valueNode).getText());
                    updatePreview();
                    apply.setDisable(false);
                    reset.setDisable(false);
                });
                break;
            }

            CheckBox cbxInherited = new CheckBox("Inherited");
            cbxInherited.setSelected(false);
            cbxInherited.setOnAction(event -> {
                if (cbxInherited.isSelected()) {
                    if (valueNode instanceof ColorPicker) {
                        ((ColorPicker) valueNode).setValue(
                                convertToColor(masterRules.get(property)));
                    }
                    else if (valueNode instanceof ComboBox<?>) {
                        ((ComboBox<String>) valueNode)
                                .setValue(masterRules.get(property));
                    }
                    else {
                        TextField tf = (TextField) valueNode;
                        String text = masterRules.get(property);
                        if (property.equals("font-size")) {
                            text = text.substring(0, text.length() - 2);
                        }
                        tf.setText(text);
                    }
                    propertyValuePairMap.put(property,
                            masterRules.get(property));
                    updatePreview();
                    apply.setDisable(false);
                    reset.setDisable(false);
                }
                valueNode.setDisable(cbxInherited.isSelected());
            });
            if (inherited) {
                valueNode.setDisable(true);
                cbxInherited.setSelected(true);
            }
            propValGrid.add(new Label(propertyLabel), 0, i);
            propValGrid.add(valueNode, 1, i);
            if (!(selected.equals("pre") || selected
                    .equals("." + NUIConstants.FILTER_COLLAPSED_TAG))) {
                propValGrid.add(cbxInherited, 2, i);
            }
            i++;
        }
    }

    private Color convertToColor(String colorStr) {
        return new Color(Integer.valueOf(colorStr.substring(1, 3), 16) / 255.0,
                Integer.valueOf(colorStr.substring(3, 5), 16) / 255.0,
                Integer.valueOf(colorStr.substring(5, 7), 16) / 255.0, 1.0);
    }

    private void updatePreview() {
        if (selected == null) {
            return;
        }
        previewWeb.getEngine().loadContent(previewPrinter
                .printPreview(cssFileHandler.parsedRulestoString(), selected));
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
        getStage().close();
    }

    @FXML
    private void handleApply() {
        try {
            cssFileHandler.writeCssFile();
        }
        catch (Exception e) {
            System.err.println("Could not write CSS File");
            e.printStackTrace();
        }

        apply.setDisable(true);
        reset.setDisable(true);
    }

    @FXML
    private void handleReset() {
        cssFileHandler.reset();
        initializeList();

        apply.setDisable(true);
        reset.setDisable(true);
    }

    @FXML
    private void handleResetDefault() {
        cssFileHandler.resetDefault();
        initializeList();

        apply.setDisable(true);
        reset.setDisable(true);
    }

}
