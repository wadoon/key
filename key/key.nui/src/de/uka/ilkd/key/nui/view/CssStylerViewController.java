/**
 * 
 */
package de.uka.ilkd.key.nui.view;

import java.io.File;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.printer.PreviewPrinter;
import de.uka.ilkd.key.nui.util.CssFileHandler;
import de.uka.ilkd.key.nui.util.CssRule;
import de.uka.ilkd.key.nui.util.NUIConstants;
import de.uka.ilkd.key.nui.util.XmlReader;
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
import javafx.scene.control.MenuItem;
import javafx.scene.control.TextField;
import javafx.scene.control.Tooltip;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.layout.GridPane;
import javafx.scene.paint.Color;
import javafx.scene.text.Font;
import javafx.scene.web.WebView;
import javafx.stage.FileChooser;
import javafx.stage.FileChooser.ExtensionFilter;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 *
 */
public class CssStylerViewController extends ViewController {
    private LinkedHashMap<String, CssRule> ruleMap = new LinkedHashMap<>();
    private String selected;
    private CssFileHandler cssFileHandler;
    private HashMap<String, String> masterRules;

    private ObservableList<String> fontWeight = FXCollections
            .observableArrayList("normal", "bold");
    private ObservableList<String> fontStyle = FXCollections
            .observableArrayList("normal", "italic");
    private ObservableList<String> fontFamily = FXCollections
            .observableArrayList(Font.getFamilies());

    private TreeItem<String> rootItem;

    private XmlReader xmlReader;

    private final static Tooltip COLOR_TT = new Tooltip(
            NUIConstants.CSSSTYLER_COLOR_TT_TEXT);
    private final static Tooltip WEIGHT_TT = new Tooltip(
            NUIConstants.CSSSTYLER_WEIGHT_TT_TEXT);
    private final static Tooltip STYLE_TT = new Tooltip(
            NUIConstants.CSSSTYLER_STYLE_TT_TEXT);
    private final static Tooltip SIZE_TT = new Tooltip(
            NUIConstants.CSSSTYLER_SIZE_TT_TEXT);
    private final static Tooltip FONT_TT = new Tooltip(
            NUIConstants.CSSSTYLER_FONT_TT_TEXT);
    private final static Tooltip INHERITED_TT = new Tooltip();

    @FXML
    private MenuItem menuOpen;
    @FXML
    private MenuItem menuSave;
    @FXML
    private MenuItem menuSaveAs;
    @FXML
    private MenuItem menuReset;
    @FXML
    private MenuItem menuResetDefault;

    @FXML
    private Button save;
    @FXML
    private Button reset;
    @FXML
    private WebView previewWeb;

    @FXML
    private TextField tfSearch;
    @FXML
    private TreeView<String> treeView;

    @FXML
    private GridPane propValGrid;

    @Override
    public void initializeAfterLoadingFxml() {
        cssFileHandler = getContext().getCssFileHandler();
        xmlReader = getContext().getXmlReader();

        initializeTree();
    }

    @Override
    public void setTooltips() {
        INHERITED_TT.setText(NUIConstants.CSSSTYLER_INHERITED_TT_TEMPLATE
                + xmlReader.getDescriptionMap().get("pre"));
    };

    /**
     * initializes the TreeView
     */
    private void initializeTree() {

        for (CssRule rule : cssFileHandler.getParsedRules()) {
            setRule(rule);
        }
        rootItem = xmlReader.getTree();
        treeView.setRoot(rootItem);
        treeView.getSelectionModel().select(0);
        treeView.requestFocus();

        treeView.getSelectionModel().selectedItemProperty().addListener(e -> {
            selected = treeView.getSelectionModel().getSelectedItem()
                    .getValue();
            updateGrid();
            updatePreview();
        });
    }

    /**
     * update the Grid with the controls associated with CSS Property
     * 
     */
    // Warning can be suppressed. Combobox can only be of Type String, as it is
    // build by the method: makeComboBox()
    @SuppressWarnings("unchecked")
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
                valueNode = makeColorPicker(value, property, COLOR_TT);
                break;
            case "color":
                propertyLabel = "Font Color:";
                valueNode = makeColorPicker(value, property, COLOR_TT);
                break;
            case "font-weight":
                propertyLabel = "Boldness:";
                valueNode = makeComboBox(fontWeight, value, property,
                        WEIGHT_TT);
                break;
            case "font-size":
                propertyLabel = "Font Size in px:";

                // Length -2 because "px" suffix in CSS
                valueNode = makeTextField(
                        value.substring(0, value.length() - 2), property, true,
                        SIZE_TT);
                break;
            case "font-family":
                propertyLabel = "Font:";
                valueNode = makeComboBox(fontFamily, value, property, FONT_TT);
                break;
            case "font-style":
                propertyLabel = "Italics:";
                valueNode = makeComboBox(fontStyle, value, property, STYLE_TT);
                break;
            case "display":
                propertyLabel = "Do not edit this rule!";
                valueNode = new Label();
                break;
            default:
                propertyLabel = property.concat(":");
                Tooltip toolTip = new Tooltip(
                        NUIConstants.CSSSTYLER_OTHER_TT_TEMPLATE + property);
                valueNode = makeTextField(value, property, toolTip);
                break;
            }
            // Logic for CSS Inheritance Handling
            CheckBox cbxInherited = new CheckBox("Inherited");

            cbxInherited.setSelected(inherited);
            valueNode.setDisable(inherited);

            cbxInherited.setTooltip(INHERITED_TT);
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
                    propertyValuePairMap.put(property, "inherit");
                    updatePreview();
                    enableControls();
                }
                valueNode.setDisable(cbxInherited.isSelected());
            });

            propValGrid.add(new Label(propertyLabel), 0, gridRow);
            propValGrid.add(valueNode, 1, gridRow);
            String selector = ruleMap.get(selected).selectorsAsString();
            if (!(selector.equals(NUIConstants.MASTER_TAG) || selector
                    .equals("." + NUIConstants.FILTER_COLLAPSED_TAG))) {
                propValGrid.add(cbxInherited, 2, gridRow);
            }
            gridRow++;
        }
    }

    /**
     * makes a TextField control for the Grid
     * 
     * @param value
     *            the initial Value
     * @param property
     *            the property to be represented by this node
     * @param toolTip
     *            a tooltip to be attached to the Combobox
     * @return a Textfield "bound" to the Css Property
     */
    private Node makeTextField(String value, String property, Tooltip toolTip) {
        return makeTextField(value, property, false, toolTip);
    }

    /**
     * makes a TextField control for the Grid
     * 
     * @param value
     *            the initial Value
     * @param property
     *            the property to be represented by this node
     * @param fontSize,
     *            a boolean indicating if this control represents the property
     *            "fontSize". If true, handles "-px" suffix for font size
     * 
     * @param toolTip
     *            a tooltip to be attached to the Combobox
     * @return a Textfield "bound" to the Css Property
     */
    private Node makeTextField(String value, String property, boolean fontSize,
            Tooltip tooltip) {
        TextField tf = new TextField(value);
        tf.setOnAction(event -> {
            if (fontSize) {
                ruleMap.get(selected).putPropertyValuePair(property,
                        tf.getText() + "px");
            }
            else {
                ruleMap.get(selected).putPropertyValuePair(property,
                        tf.getText());
            }

            updatePreview();
            enableControls();
        });

        tf.setTooltip(tooltip);
        return tf;
    }

    /**
     * makes a ComboBox control for the Grid
     * 
     * @param comboList
     *            the list containing all the options for this comboBox
     * @param value
     *            the initial Value
     * @param property
     *            the property to be represented by this node
     * 
     * @param toolTip
     *            a tooltip to be attached to the Combobox
     * @return a ComboBox "bound" to the Css Property
     */
    private Node makeComboBox(ObservableList<String> comboList, String value,
            String property, Tooltip toolTip) {
        ComboBox<String> cb = new ComboBox<>(comboList);
        cb.setValue(value);
        cb.setOnAction(event -> {
            ruleMap.get(selected).putPropertyValuePair(property, cb.getValue());
            updatePreview();
            enableControls();
        });
        cb.setTooltip(toolTip);
        return cb;
    }

    /**
     * makes a ColorPicker control, if the Color can be parsed, and a TextArea
     * if else
     * 
     * @param value
     *            the initial value
     * @param property
     *            the property to be represented by this node
     * @param toolTip
     *            a tooltip to be attached to the Combobox
     * @return a ColorPicker if the initial value can be parsed as a Color, a
     *         TextArea if else. This node is then "bound" to the Css Property
     */
    private Node makeColorPicker(String value, String property,
            Tooltip toolTip) {
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
                enableControls();
            });
            cp.setTooltip(toolTip);
            node = cp;
        }
        // Catch all the Exceptions. If a CSS Value cannot be converted into a
        // color, an error gets thrown. This is catched and a simple Textfield
        // used instead.
        catch (Exception e) {
            System.err.println("Could not read Color. Using TextField");
            node = makeTextField(value, property, toolTip);
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
        previewWeb.getEngine().loadContent(PreviewPrinter.printPreview(
                cssFileHandler.parsedRulestoString(), ruleMap.get(selected)));
    }

    @FXML
    private void handleSearch() {
        decollapseChildren(rootItem, tfSearch.getText());
    }

    private void decollapseChildren(TreeItem<String> root,
            String searchString) {
        if (searchString == null || searchString.isEmpty()) {
            return;
        }

        if (root.getValue().toLowerCase(Locale.ENGLISH)
                .contains(searchString.toLowerCase(Locale.ENGLISH))) {
            root.setExpanded(true);
        }
        for (TreeItem<String> child : root.getChildren()) {
            if (child.isLeaf()) {
                if (child.getValue().toLowerCase(Locale.ENGLISH)
                        .contains(searchString.toLowerCase(Locale.ENGLISH))) {
                    root.setExpanded(true);
                    treeView.getSelectionModel().select(child);
                }
            }
            else {
                decollapseChildren(child, searchString);
            }
        }
    }

    @FXML
    private void handleExit() {
        if (save.disabledProperty().get() == false) {
            Alert alert = getMainApp().createAlert("Confirm Exit",
                    "Do you want to save your changes?",
                    "Unsaved changes will be lost upon exit",
                    AlertType.CONFIRMATION);

            ButtonType saveExit = new ButtonType("Save and Exit");
            ButtonType resetExit = new ButtonType("Exit without Saving");
            ButtonType cancel = new ButtonType("Cancel",
                    ButtonData.CANCEL_CLOSE);

            alert.getButtonTypes().setAll(saveExit, resetExit, cancel);

            Optional<ButtonType> result = alert.showAndWait();
            if (result.get() == saveExit) {
                handleSave();
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
    private void handleSave() {
        if (cssFileHandler.getPath().isEmpty() || cssFileHandler.getPath()
                .equals(NUIConstants.DEFAULT_CSS_PATH)) {
            handleSaveAs();
        }
        else {
            writeToCss();
        }
    }

    @FXML
    private void handleSaveAs() {

        File file = makeFileChooser().showSaveDialog(getStage());

        if (file != null) {
            cssFileHandler.setPath(file.getAbsolutePath());
            writeToCss();
        }
    }

    @FXML
    private void handleOpen() {
        File file = makeFileChooser().showOpenDialog(getStage());

        if (file != null) {
            try {
                cssFileHandler.loadCssFile(file.getAbsolutePath());
            }
            catch (Exception e) {
                System.err.println("Could not load CSS File");
            }
        }
        resetUI();

    }

    private FileChooser makeFileChooser() {
        FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle("Select a CSS File");
        fileChooser.getExtensionFilters().addAll(
                new ExtensionFilter("CSS File", "*.css"),
                new ExtensionFilter("All Files", "*.*"));
        return fileChooser;
    }

    private void writeToCss() {
        try {
            cssFileHandler.writeCssFile();
        }
        catch (Exception e) {
            System.err.println("Could not write CSS File");
            e.printStackTrace();
        }

        disableControls();
    }

    /**
     * sets the ruleInformation used by the grid
     */
    private void setRule(CssRule rule) {
        Map<String, String> descriptionMap = xmlReader.getDescriptionMap();

        String ruleDescription = descriptionMap.get(rule.selectorsAsString());

        if (ruleDescription == null) {
            ruleDescription = rule.selectorsAsString();
        }
        if (rule.selectorsAsString().equals(NUIConstants.MASTER_TAG)) {
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
     * enables all the buttons in the Bar
     */
    private void enableControls() {
        menuSave.setDisable(false);
        menuReset.setDisable(false);

        save.setDisable(false);
        reset.setDisable(false);
    }

    private void disableControls() {
        menuSave.setDisable(true);
        menuReset.setDisable(true);

        save.setDisable(true);
        reset.setDisable(true);
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
        disableControls();
    }

    @FXML
    private void handleResetDefault() {
        cssFileHandler.resetDefault();
        resetUI();
    }

}
