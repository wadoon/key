/**
 * 
 */
package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Optional;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.util.CssFileHandler;
import de.uka.ilkd.key.nui.util.CssRule;
import de.uka.ilkd.key.nui.util.NUIConstants;
import de.uka.ilkd.key.nui.util.PreviewPrinter;
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
import javafx.scene.control.TextField;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.layout.GridPane;
import javafx.scene.paint.Color;
import javafx.scene.web.WebView;

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
    private TreeView<String> treeView;
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

        initializeTree();
    }

    /**
     * initializes the TreeView
     */
    private void initializeTree() {
        // Root for Tree
        TreeItem<String> rootItem = new TreeItem<String>(
                "Sequent Style Settings");
        // SetUp Categories
        rootItem.getChildren().add(new TreeItem<String>("General Settings"));
        rootItem.getChildren().add(new TreeItem<String>("Filter Settings"));
        rootItem.getChildren().add(new TreeItem<String>("Rule Application"));
        rootItem.getChildren().add(new TreeItem<String>("Operators"));
        rootItem.getChildren().add(new TreeItem<String>("Logic Terms"));
        rootItem.getChildren().add(new TreeItem<String>("Function Terms"));
        rootItem.getChildren().add(new TreeItem<String>("Java Styling"));
        rootItem.getChildren()
                .add(new TreeItem<String>("Conditional Operators"));
        rootItem.getChildren().add(new TreeItem<String>("Updater"));
        rootItem.getChildren().add(new TreeItem<String>("Schema Variables"));
        rootItem.getChildren().add(new TreeItem<String>("Other Settings"));

        // For every rule: get Description from Constants and Sort into Tree
        for (CssRule rule : cssFileHandler.getParsedRules()) {
            String ruleDescription = NUIConstants.getClassDescriptionMap()
                    .get(rule.selectorsAsString());

            if (ruleDescription == null) {
                ruleDescription = rule.selectorsAsString();
            }

            switch (rule.selectorsAsString()) {
            case "pre":
                masterRules = rule.getPropertyValuePairs();
            case "." + NUIConstants.HIGHLIGHTED_TAG:
            case "." + NUIConstants.MOUSE_TAG:
                // General Settings
                rootItem.getChildren().get(0).getChildren()
                        .add(new TreeItem<String>(ruleDescription));
                break;
            case "." + NUIConstants.FILTER_SELECTION_TAG:
            case "." + NUIConstants.FILTER_MINIMIZED_TAG:
            case "." + NUIConstants.FILTER_COLLAPSED_TAG:
                // Filter Settings
                rootItem.getChildren().get(1).getChildren()
                        .add(new TreeItem<String>(ruleDescription));
                break;
            case "." + NUIConstants.RULE_APP_TAG:
            case "." + NUIConstants.IF_INST_TAG:
            case "." + NUIConstants.IF_FORMULA_TAG:
                // Rule Application
                rootItem.getChildren().get(2).getChildren()
                        .add(new TreeItem<String>(ruleDescription));
                break;
            case "." + NUIConstants.ELEMUPDATE_TAG:
            case "." + NUIConstants.EQUALITY_TAG:
            case "." + NUIConstants.JUNCTOR_TAG:
            case "." + NUIConstants.SUBSTOP_TAG:
            case "." + NUIConstants.WARYSUBSTOP_TAG:
                // Operator
                rootItem.getChildren().get(3).getChildren()
                        .add(new TreeItem<String>(ruleDescription));
                break;
            case "." + NUIConstants.LOGICVAR_TAG:
            case "." + NUIConstants.OBSERVERFUNC_TAG:
            case "." + NUIConstants.QUANTIFIER_TAG:
                // Logic Terms
                rootItem.getChildren().get(4).getChildren()
                        .add(new TreeItem<String>(ruleDescription));
                break;
            case "." + NUIConstants.FUNCTION_TAG:
            case "." + NUIConstants.SORTDEPFUNC_TAG:
            case "." + NUIConstants.TRANSFORMER_TAG:
            case "." + NUIConstants.VARSV_TAG:
                // Function Terms
                rootItem.getChildren().get(5).getChildren()
                        .add(new TreeItem<String>(ruleDescription));
                break;
            case "." + NUIConstants.MODALITY_TAG:
            case "." + NUIConstants.MODALOPSV_TAG:
            case "." + NUIConstants.LOCATIONVAR_TAG:
            case "." + NUIConstants.PROGCONST_TAG:
            case "." + NUIConstants.PROGMETH_TAG:
            case "." + NUIConstants.PROGSV_TAG:
            case "." + NUIConstants.PROGVAR_TAG:
                // Java Styling
                rootItem.getChildren().get(6).getChildren()
                        .add(new TreeItem<String>(ruleDescription));
                break;
            case "." + NUIConstants.IFEXTHENELSE_TAG:
            case "." + NUIConstants.IFTHENELSE_TAG:
                // Cond. Operator
                rootItem.getChildren().get(7).getChildren()
                        .add(new TreeItem<String>(ruleDescription));
                break;
            case "." + NUIConstants.UPDATEAPP_TAG:
            case "." + NUIConstants.UPDATEJUNC_TAG:
            case "." + NUIConstants.UPDATESV_TAG:
                // Update Terms
                rootItem.getChildren().get(8).getChildren()
                        .add(new TreeItem<String>(ruleDescription));
                break;
            case "." + NUIConstants.FORMULASV_TAG:
            case "." + NUIConstants.SCHEMAVARFACTORY_TAG:
            case "." + NUIConstants.TERMLABELSV_TAG:
            case "." + NUIConstants.TERMSV_TAG:
            case "." + NUIConstants.SKOLEMTERMSV_TAG:
                // Schema Variable
                rootItem.getChildren().get(9).getChildren()
                        .add(new TreeItem<String>(ruleDescription));
                break;
            default:
                // Default: Other
                rootItem.getChildren().get(rootItem.getChildren().size() - 1)
                        .getChildren()
                        .add(new TreeItem<String>(ruleDescription));
                break;
            }
            setRule(rule);
        }

        treeView.setRoot(rootItem);

        treeView.getSelectionModel().selectedItemProperty().addListener(e -> {
            selected = treeView.getSelectionModel().getSelectedItem()
                    .getValue();
            updateGrid();
            updatePreview();
        });
    }

    /**
     * update the Grid with the controls associated with CSS Property
     */
    private void updateGrid() {
        if (selected == null || !ruleMap.containsKey(selected)) {
            return;
        }

        propValGrid.getChildren().clear();

        HashMap<String, String> propertyValuePairMap = ruleMap.get(selected)
                .getPropertyValuePairs();

        int gridRow = 0;
        for (String property : propertyValuePairMap.keySet()) {
            String value = propertyValuePairMap.get(property);
            String propertyLabel;
            Node valueNode;
            boolean inherited = false;

            // necessary to have info about inherited values
            if (value.equals("inherit")) {
                value = masterRules.get(property);
                inherited = true;
            }

            switch (property) {
            case "background-color":
                propertyLabel = "Background Color:";
                valueNode = makeColorPicker(value, property);
                break;
            case "color":
                propertyLabel = "Font Color:";
                valueNode = makeColorPicker(value, property);
                break;
            case "font-weight":
                propertyLabel = "Boldness:";
                valueNode = makeComboBox(fontWeight, value, property);
                break;
            case "font-size":
                propertyLabel = "Font Size in px:";

                // Length -2 because "px" suffix in CSS
                valueNode = makeTextField(
                        value.substring(0, value.length() - 2), property);
                break;
            case "font-family":
                propertyLabel = "Font:";
                valueNode = makeComboBox(fontFamily, value, property);
                break;
            case "font-style":
                propertyLabel = "Italics:";
                valueNode = makeComboBox(fontStyle, value, property);
                break;
            case "display":
                propertyLabel = "Do not edit this rule!";
                valueNode = new Label();
                break;
            default:
                propertyLabel = property;
                valueNode = makeTextField(value, property);
                break;
            }
            //Logic for CSS Inheritance Handling
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

            propValGrid.add(new Label(propertyLabel), 0, gridRow);
            propValGrid.add(valueNode, 1, gridRow);
            String selector = ruleMap.get(selected).selectorsAsString();
            if (!(selector.equals("pre") || selector
                    .equals("." + NUIConstants.FILTER_COLLAPSED_TAG))) {
                propValGrid.add(cbxInherited, 2, gridRow);
            }
            gridRow++;
        }
    }

    private Node makeTextField(String value, String property) {
        TextField tf = new TextField(value);
        tf.setOnAction(event -> {
            ruleMap.get(selected).putPropertyValuePair(property, tf.getText());
            updatePreview();
            apply.setDisable(false);
            reset.setDisable(false);
        });

        return tf;
    }

    private Node makeComboBox(ObservableList<String> comboList, String value,
            String property) {
        ComboBox<String> cb = new ComboBox<>(comboList);
        cb.setValue(value);
        cb.setOnAction(event -> {
            ruleMap.get(selected).putPropertyValuePair(property, cb.getValue());
            updatePreview();
            apply.setDisable(false);
            reset.setDisable(false);
        });
        return cb;
    }

    private Node makeColorPicker(String value, String property) {
        Node node;
        try {
            ColorPicker cp = new ColorPicker(convertToColor(value));
            cp.setOnAction(event -> {
                Color c = cp.getValue();

                ruleMap.get(selected).putPropertyValuePair(property,
                        String.format("#%02X%02X%02X", (int) (c.getRed() * 255),
                                (int) (c.getGreen() * 255),
                                (int) (c.getBlue() * 255)));
                updatePreview();
                apply.setDisable(false);
                reset.setDisable(false);
            });
            node = cp;
        }
        catch (Exception e) {
            System.err.println("Could not read Color. Using TextField");
            node = makeTextField(value, property);
        }
        
        return node;
    }

    /**
     * converts a hexstring with prefixed # into a Color Object
     * 
     * @param colorStr
     *            the string
     * @return a Color Object
     */
    private Color convertToColor(String colorStr) {
        return new Color(Integer.valueOf(colorStr.substring(1, 3), 16) / 255.0,
                Integer.valueOf(colorStr.substring(3, 5), 16) / 255.0,
                Integer.valueOf(colorStr.substring(5, 7), 16) / 255.0, 1.0);
    }

    /**
     * updates the previewWeb component using the currently selected CSS class
     */
    private void updatePreview() {
        if (selected == null || !ruleMap.containsKey(selected)) {
            return;
        }
        previewWeb.getEngine().loadContent(previewPrinter.printPreview(
                cssFileHandler.parsedRulestoString(), ruleMap.get(selected)));
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

    /**
     * sets the ruleInformation used by the grid
     */
    private void setRule(CssRule rule) {
        String ruleDescription = NUIConstants.getClassDescriptionMap()
                .get(rule.selectorsAsString());

        if (ruleDescription == null) {
            ruleDescription = rule.selectorsAsString();
        }
        if (rule.selectorsAsString().equals("pre")) {
            masterRules = rule.getPropertyValuePairs();
        }

        ruleMap.put(ruleDescription, rule);
    }

    @FXML
    private void handleReset() {
        cssFileHandler.reset();
        resetUI();
    }

    /**
     * resets the complete UI
     */
    private void resetUI() {
        for (CssRule rule : cssFileHandler.getParsedRules()) {
            setRule(rule);
        }
        updateGrid();
        updatePreview();
        apply.setDisable(true);
        reset.setDisable(true);
    }

    @FXML
    private void handleResetDefault() {
        cssFileHandler.resetDefault();
        resetUI();
    }

}
