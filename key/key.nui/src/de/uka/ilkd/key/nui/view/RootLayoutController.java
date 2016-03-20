/**
 * 
 */
package de.uka.ilkd.key.nui.view;

import java.io.File;
import java.net.URL;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.MainApp;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewInformation;
import de.uka.ilkd.key.nui.ViewObserver;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.ViewSlot;
import de.uka.ilkd.key.nui.util.NUIConstants;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.UnicodeHelper;
import javafx.application.Platform;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.Node;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SplitPane;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.TransferMode;
import javafx.scene.layout.BorderPane;
import javafx.stage.FileChooser;
import javafx.stage.Stage;
import javafx.stage.FileChooser.ExtensionFilter;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 * @author Benedikt Gross
 * @author Nils Muzzulini
 */
public class RootLayoutController extends ViewController {

    private static final int MAXMENUENTRIES = 8;
    private static final Image STATUSLOGO = new Image(
            "file:resources/images/key-color-transparent-background.png");
    private static final String STATUSWELCOMETEXT = KeYConstants.COPYRIGHT
            + "\nKeY is free Software and comes with ABSOLUTELY NO WARRANTY";

    private HashMap<ViewPosition, ViewSlot> viewSlots = new HashMap<>();
    private HashMap<Integer, ViewInformation> allViews = new HashMap<>();
    private File file;

    /**
     * The BorderPane from the Main Window
     */
    @FXML
    private BorderPane mainPane;

    /**
     * The Splitpane in the BorderPane Center, Root of AnchorPane Positions
     */
    @FXML
    private SplitPane mainSplitPane;

    /**
     * SplitPanes left and right
     */
    @FXML
    private SplitPane leftPane;
    @FXML
    private SplitPane rightPane;

    /**
     * The AnchorPane Positions
     */
    @FXML
    private BorderPane topLeft;
    @FXML
    private BorderPane bottomLeft;
    @FXML
    private BorderPane center;
    @FXML
    private BorderPane topRight;
    @FXML
    private BorderPane bottomRight;

    @FXML
    private MenuBar menuBar;
    @FXML
    private Menu helpMenu;
    @FXML
    private Label statusLabel;
    @FXML
    private ButtonBar debugButtons;
    @FXML
    private CheckMenuItem debugMode;

    /**
     * The constructor
     */
    public RootLayoutController() {

    }

    /**
     * Called once when the rootlayout is loaded.
     */
    @Override
    public void initialize(URL location, ResourceBundle resources) {
        ViewSlot.setRegisterDrag(node -> {
            node.setOnDragOver(event -> {
                if (event.getGestureSource() != node) {
                    event.acceptTransferModes(TransferMode.MOVE);
                }
                event.consume();
            });
            node.setOnDragEntered(event -> {
                if (event.getGestureSource() != node) {
                    // node.setEffect(new Glow());
                    node.setStyle(
                            "-fx-padding: 1; -fx-background-color: yellow, -fx-control-inner-background; -fx-background-insets: 0, 1;");
                }
                event.consume();
            });
            node.setOnDragExited(event -> {
                // node.setEffect(null);
                node.setStyle("");
                event.consume();
            });
            node.setOnDragDropped(event -> {
                boolean success = false;
                if (event.getDragboard().hasString()) {
                    String id = event.getDragboard().getString();
                    allViews.get(Integer.parseInt(id))
                            .setCurrentPosition(getTabPosition(node));
                    success = true;
                }
                event.setDropCompleted(success);
                event.consume();
            });
        });
        viewSlots.put(ViewPosition.BOTTOMLEFT,
                new ViewSlot(ViewPosition.BOTTOMLEFT, bottomLeft));
        viewSlots.put(ViewPosition.BOTTOMRIGHT,
                new ViewSlot(ViewPosition.BOTTOMRIGHT, bottomRight));
        viewSlots.put(ViewPosition.CENTER,
                new ViewSlot(ViewPosition.CENTER, center));
        viewSlots.put(ViewPosition.TOPLEFT,
                new ViewSlot(ViewPosition.TOPLEFT, topLeft));
        viewSlots.put(ViewPosition.TOPRIGHT,
                new ViewSlot(ViewPosition.TOPRIGHT, topRight));

        statusLabel.setGraphic(new ImageView(STATUSLOGO));
        statusLabel.setText(STATUSWELCOMETEXT);

        if (!MainApp.isDebugView()) {
            debugButtons.setOpacity(0);
            debugButtons.setDisable(true);
            debugMode.setSelected(false);
        }
    }

    @Override
    public void initializeAfterLoadingFxml() {
        getContext().getStatusManager().getStatusUpdatedEvent()
                .addHandler(this::setStatus);
    };

    /**
     * Shows a dialog with information about KeY.
     * 
     * @param event
     *            ActionEvent
     */
    @FXML
    private void handleAbout(ActionEvent event) {
        getMainApp().showAlert("About KeY", "The KeY Project",
                KeYConstants.COPYRIGHT.replace("and",
                        "\n" + UnicodeHelper.emSpaces(8) + "and")
                        + "\n\nWWW: http://key-project.org/" + "\n\nVersion "
                        + KeYConstants.VERSION,
                AlertType.INFORMATION);
    }

    /**
     * Loads a default closed proof.
     */
    @FXML
    private void loadDefaultProof() {
        getContext().getKeYMediator().getUI()
                .loadProblem(new File("resources/proofs/gcd.closed.proof"));
    }

    /**
     * Loads a large sample open proof.
     */
    @FXML
    private void loadBigProof() {
        getContext().getKeYMediator().getUI().loadProblem(
                new File("resources/SampleProof/sampleProof.proof"));
    }

    /**
     * Loads a simple key file to test proof splitting.
     */
    @FXML
    private void loadProofSplitTest() {
        getContext().getKeYMediator().getUI()
                .loadProblem(new File("resources/proofs/testSplit.key"));
    }

    /**
     * Loads a simple key file to test model search vs basic arithmetic
     * treatment.
     */
    @FXML
    private void loadModelSearchVsBasicTest() {
        getContext().getKeYMediator().getUI().loadProblem(
                new File("resources/proofs/testModelSearchVsBasic.key"));
    }

    /**
     * Loads an open solvable proof.
     */
    @FXML
    private void loadSolvableProof() {
        getContext().getKeYMediator().getUI().loadProblem(new File(
                "resources/proofs/IndistinguishablePathConditions.proof"));
    }

    /**
     * Loads an open unsolvable proof.
     */
    @FXML
    private void loadUnsolvableProof() {
        getContext().getKeYMediator().getUI().loadProblem(new File(
                "resources/proofs/IndistinguishablePathConditions.twoJoins.proof"));
    }

    @FXML
    private void handleDebugMode() {
        if (debugMode.isSelected()) {
            debugButtons.setOpacity(100.00);
            debugButtons.setDisable(false);
        }
        else {
            debugButtons.setOpacity(0);
            debugButtons.setDisable(true);
        }
    }

    /**
     * Exits the program on Click.
     */
    @FXML
    private void handleExit() {
        getMainApp().closeWindowAlert();
    }

    /**
     * Opens a file chooser to choose a proof to be loaded.
     */
    @FXML
    private void handleOpen() {
        setStatus("Loading Proof...");
        FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle("Select a proof to load");
        fileChooser.getExtensionFilters()
                .addAll(new ExtensionFilter("Proofs, KeY or Java Files",
                        "*.proof", "*.key", "*.java"),
                new ExtensionFilter("All Files", "*.*"));

        if (file != null) {
            File existDirectory = file.getParentFile();
            fileChooser.setInitialDirectory(existDirectory);
        }
        else {
            // TODO reset initial directory to "../" (changed for faster access
            // to
            // proofs for testing purposes)
            fileChooser.setInitialDirectory(
                    new File("../key.core.test/resources/testcase/join"));
        }

        file = fileChooser.showOpenDialog(null);

        if (file == null) {
            setStatus("No File Selected");
            return;
        }
        getContext().getKeYMediator().getUI().loadProblem(file);
    }

    private void setStatus(String status) {
        // execute ui update on javafx thread
        Platform.runLater(() -> {
            statusLabel.setText(status);
        });
    }

    @FXML
    private Menu viewsMenu;

    private Menu otherViewsMenu = null;

    /**
     * Sets selected to active where the menuitems title matches the given
     * title.
     * 
     * @param title
     *            The title of the menuitem which should be changed
     * @param active
     *            true for check, false for uncheck
     */
    public void checkViewMenuItem(String title, boolean active) {
        List<MenuItem> items = new LinkedList<>(viewsMenu.getItems());
        if (otherViewsMenu != null)
            items.addAll(otherViewsMenu.getItems());
        for (MenuItem item : items) {
            if (item.getText().equals(title)) {
                if (item instanceof CheckMenuItem) {
                    // TODO: prevent triggering selected. not critical since the
                    // observer also handles that
                    ((CheckMenuItem) item).setSelected(active);
                }
                break;
            }
        }
    }

    /**
     * 
     * @param info
     * @param accelerator
     */
    public void registerView(ViewInformation info, String accelerator) {
        allViews.put(info.getId(), info);
        if (info.hasMenuItem()) {
            CheckMenuItem item = new CheckMenuItem();
            item.setText(info.getTitle());
            item.selectedProperty().addListener((ov, oldValue, newValue) -> {
                info.setIsActive(newValue);
                resize();
            });
            item.setSelected(info.getIsActive());
            if (!accelerator.equals(""))
                item.setAccelerator(KeyCombination.valueOf(accelerator));

            // make overflow menu "Others" if items exceed max
            if (viewsMenu.getItems().size() < MAXMENUENTRIES) {
                viewsMenu.getItems().add(item);
            }
            else {
                if (otherViewsMenu == null) {
                    otherViewsMenu = new Menu("Other");
                    viewsMenu.getItems().add(otherViewsMenu);
                }
                otherViewsMenu.getItems().add(item);
            }
        }
    }

    /**
     * Shows view at its preferred viewposition
     * 
     * @param view
     */
    public void showView(ViewInformation view) {
        if (view.getUiTab() == null) {
            view.loadUiTab(this);
        }
        setPosition(view, view.getCurrentPosition());
    }

    /**
     * Hides the view which belongs to given ViewInformation
     * 
     * @param view
     */
    public void hideView(ViewInformation view) {
        // XXX: workaround
        loop: for (ViewSlot slot : viewSlots.values()) {
            for (ViewInformation info : slot.getTabs()) {
                if (info == view) {
                    slot.removeTab(view);
                    updateViewUsed(slot);
                    break loop;
                }
            }
        }
        resize();
    }

    /**
     * updates the field "pastUsed" for all ViewSlots EXCEPT the argument.
     * Necessary for resizing
     * 
     * @param slot
     *            the only slot NOT to be updated by this function. This slot is
     *            updated by it's private add/remove Tab methods!!
     */
    private void updateViewUsed(ViewSlot slot) {
        for (ViewSlot loopSlot : viewSlots.values()) {
            if (loopSlot != slot) {
                loopSlot.updatePastUsed();
            }
        }
    }

    private void setPosition(ViewInformation view, ViewPosition position) {
        viewSlots.get(position).addTab(view);
        updateViewUsed(viewSlots.get(position));
        resize();
    }

    /**
     * Moves the view which belongs to given ViewInformation to ViewPosition
     * next
     * 
     * @param view
     * @param next
     */
    public void moveView(ViewInformation view, ViewPosition next) {
        hideView(view);
        setPosition(view, next);
    }

    /**
     * @param node
     * @return
     */
    public ViewPosition getTabPosition(Node node) {
        for (ViewSlot slot : viewSlots.values()) {
            if (slot.getUiPane().getChildren().size() == 1
                    && slot.getUiPane().getChildren().get(0) == node)
                return slot.getViewPosition();
        }
        return null;
    }

    /**
     * @param node
     * @return ViewPosition where the given node is currently placed.
     */
    public ViewPosition getViewPosition(Node node) {
        for (ViewSlot slot : viewSlots.values()) {
            if (slot.getUiPane() == node)
                return slot.getViewPosition();
        }
        return null;
    }

    /**
     * Resizes the splitpanes which build the main frame TODO needs to be
     * redone, as it currently is kind of a hack.
     */
    public void resize() {
        ViewSlot topLeft = viewSlots.get(ViewPosition.TOPLEFT);
        ViewSlot bottomLeft = viewSlots.get(ViewPosition.BOTTOMLEFT);
        ViewSlot topRight = viewSlots.get(ViewPosition.TOPRIGHT);
        ViewSlot bottomRight = viewSlots.get(ViewPosition.BOTTOMRIGHT);
        double[] dividerPositions = mainSplitPane.getDividerPositions();
        double leftDivider = leftPane.getDividerPositions()[0];
        double rightDivider = rightPane.getDividerPositions()[0];

        // If topLeft has changed
        if (topLeft.getUsed() != topLeft.getPastUsed()) {
            if (!bottomLeft.getUsed()) {
                if (topLeft.getUsed()) {
                    mainSplitPane.setDividerPosition(0, 0.3);
                    leftPane.setDividerPositions(1.0);
                }
                else {
                    mainSplitPane.setDividerPosition(0, 0.0);
                }
            }
            else {
                if (topLeft.getUsed()) {
                    leftPane.setDividerPositions(0.5);
                }
                else {
                    leftPane.setDividerPositions(0.0);
                }
            }
            return;
        }
        // If bottomLeft has changed
        if (bottomLeft.getUsed() != bottomLeft.getPastUsed()) {
            if (!topLeft.getUsed()) {
                if (bottomLeft.getUsed()) {
                    mainSplitPane.setDividerPosition(0, 0.3);
                    leftPane.setDividerPositions(0.0);
                }
                else {
                    mainSplitPane.setDividerPosition(0, 0.0);
                }
            }
            else {
                if (bottomLeft.getUsed()) {
                    leftPane.setDividerPositions(0.5);
                }
                else {
                    leftPane.setDividerPositions(1.0);
                }
            }
            return;
        }
        // If topRight has changed
        if (topRight.getUsed() != topRight.getPastUsed()) {
            if (!bottomRight.getUsed()) {
                if (topRight.getUsed()) {
                    mainSplitPane.setDividerPosition(1, 0.7);
                    rightPane.setDividerPositions(1.0);
                }
                else {
                    mainSplitPane.setDividerPosition(1, 1.0);
                }
            }
            else {
                if (topRight.getUsed()) {
                    rightPane.setDividerPositions(0.5);
                }
                else {
                    rightPane.setDividerPositions(0.0);
                }
            }
            return;
        }
        // If bottomRight has changed
        if (bottomRight.getUsed() != bottomRight.getPastUsed()) {
            if (!topRight.getUsed()) {
                if (bottomRight.getUsed()) {
                    mainSplitPane.setDividerPosition(1, 0.7);
                    rightPane.setDividerPositions(0.0);
                }
                else {
                    mainSplitPane.setDividerPosition(1, 1.0);
                }
            }
            else {
                if (bottomRight.getUsed()) {
                    rightPane.setDividerPositions(0.5);
                }
                else {
                    rightPane.setDividerPositions(1.0);
                }
            }
            return;
        }
        mainSplitPane.setDividerPositions(dividerPositions);
        leftPane.setDividerPositions(leftDivider);
        rightPane.setDividerPositions(rightDivider);
    }

    /**
     * 
     * @param sourcePath
     */
    public void registerMenu(URL sourcePath) {
        // add additional menus right before the "Help" entry
        menuBar.getMenus().add(menuBar.getMenus().indexOf(helpMenu),
                loadFxmlFromContext(sourcePath));
    }

    public void registerMenuEntry(URL sourcePath, String parentMenu)
            throws IllegalStateException {
        for (Menu m : menuBar.getMenus()) {
            if (m.getText().equals(parentMenu)) {
                m.getItems().add(loadFxmlFromContext(sourcePath));
                return;
            }
        }
        throw new IllegalStateException(
                "Menu " + parentMenu + " was not found");
    }

    /**
     * size = 4 : left-vertical, left-horizontal, right-vertical,
     * right-horizontal
     */
    public List<Double> getSplitterPositions() {
        double[] vertical = mainSplitPane.getDividerPositions();
        return Arrays.asList(vertical[0], leftPane.getDividerPositions()[0],
                vertical[1], rightPane.getDividerPositions()[0]);
    }

    public List<ViewInformation> getViewInformations() {
        return new LinkedList<ViewInformation>(allViews.values());
    }

    /**
     * size = 4 : left-vertical, left-horizontal, right-vertical,
     * right-horizontal
     */
    public void setSplitterPositions(List<Double> positions) {
        mainSplitPane.setDividerPositions(positions.get(0), positions.get(2));
        leftPane.setDividerPositions(positions.get(1));
        rightPane.setDividerPositions(positions.get(3));
    }

    @FXML
    private void handleSequentCssStylerAction() {
        getMainApp().openNewWindow("Sequent CSS Styler",
                "view/CssStylerView.fxml", true, true);
    }

    @FXML
    private void openInNew() {
        de.uka.ilkd.key.proof.Node node = getContext().getKeYMediator()
                .getSelectedNode();

        ViewInformation info = new ViewInformation(
                node.serialNr() + ": " + node.name(),
                StaticSequentViewController.class.getResource(
                        "StaticSequentView.fxml"),
                ViewPosition.CENTER, false);

        // if moved to other menu outside of RootLayoutController, swap the
        // following lines
        // info.addObserver(new
        // ViewObserver(getMainApp().getRootLayoutController()));
        // getMainApp().getRootLayoutController().registerView(info, "");
        info.addObserver(new ViewObserver(this));
        this.registerView(info, "");

        info.setIsActive(true);

        Platform.runLater(() -> {
            ((StaticSequentViewController) info.getController())
                    .getSequentViewController().loadNodeToView(node);
        });
    }
}
