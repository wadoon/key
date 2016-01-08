/**
 * 
 */
package de.uka.ilkd.key.nui.view;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.MainApp;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.ViewInformation;
import de.uka.ilkd.key.nui.model.ViewSlot;
import de.uka.ilkd.key.nui.util.IStatusManager;
import javafx.application.Platform;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SplitPane;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.input.ClipboardContent;
import javafx.scene.input.Dragboard;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.TransferMode;
import javafx.scene.layout.BorderPane;
import javafx.stage.FileChooser;
import javafx.stage.FileChooser.ExtensionFilter;
import javafx.stage.Stage;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 * @author Benedikt Gross
 * @author Nils Muzzulini
 */
public class RootLayoutController extends ViewController
        implements IStatusManager {

    private static final int MAXMENUENTRIES = 8;
    private static final Image STATUSLOGO = new Image(
            "file:resources/images/key-color.gif");
    private static final String STATUSWELCOMETEXT = "\u00a9 Copyright 2001 - 2016 Karlsruhe Institute of Technology, Chalmers University of Technology, and Technische Universitaet Darmstadt \n"
            + "KeY is free Software and comes with ABSOLUTELY NO WARRANTY";

    @FXML
    private Label statusLabel;

    private HashMap<ViewPosition, ViewSlot> viewSlots = new HashMap<>();
    private HashMap<Integer, ViewInformation> allViews = new HashMap<>();

    /**
     * The BorderPane from the Main Window
     */
    @FXML
    BorderPane mainPane;

    /**
     * The Splitpane in the BorderPane Center, Root of AnchorPane Positions
     */
    @FXML
    SplitPane mainSplitPane;

    /**
     * SplitPanes left and right
     */
    @FXML
    SplitPane leftPane;
    @FXML
    SplitPane rightPane;

    /**
     * The AnchorPane Positions
     */
    @FXML
    BorderPane topLeft;
    @FXML
    BorderPane bottomLeft;
    @FXML
    BorderPane center;
    @FXML
    BorderPane topRight;
    @FXML
    BorderPane bottomRight;

    @FXML
    private MenuBar menuBar;

    @FXML
    private Menu helpMenu;

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
    }

    /**
     * Opens a new Window with About Functionality. View: AboutView.fxml
     * 
     * @param event
     *            ActionEvent
     */
    @FXML
    private void handleAbout(ActionEvent event) {
        try {
            FXMLLoader loader = new FXMLLoader();
            loader.setLocation(
                    MainApp.class.getResource("view/AboutView.fxml"));

            Stage stage = new Stage();
            stage.setTitle("About Key");

            stage.setScene(new Scene((BorderPane) loader.load()));

            stage.show();

        }
        catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Closes the program on Click
     */
    @FXML
    private void handleClose() {
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
        fileChooser.getExtensionFilters().addAll(
                new ExtensionFilter("Proofs", "*.proof"),
                new ExtensionFilter("All Files", "*.*"));
        // TODO reset initial directory to "../" (changed for faster access to
        // proofs for testing purposes)
        fileChooser.setInitialDirectory(
                new File("../key.core.test/resources/testcase/join"));

        File file = fileChooser.showOpenDialog(new Stage());

        if (file == null) {
            setStatus("No File Selected");
            return;
        }
        getContext().getProofManager().loadProblem(file);
    }

    /**
     * Set a status in the status bar.
     * 
     * @param status
     *            Status to be set.
     */
    public void setStatus(String status) {
        // execute ui update on javafx thread
        Platform.runLater(() -> {
            statusLabel.setText(status);
        });
        System.out.println(status);
    }

    /**
     * Sets status text to empty string.
     */
    public void clearStatus() {
        setStatus("");
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
        //TODO: dummy until last opened or config was developed
        info.setIsActive(true);
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
        setPosition(view, view.getPreferedPosition());
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
                    break loop;
                }
            }
        }
        resize();
    }

    private void setPosition(ViewInformation view, ViewPosition position) {
        viewSlots.get(position).addTab(view);
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
        mainSplitPane.setDividerPositions(0.0, 1.0);
        if (viewSlots.get(ViewPosition.TOPLEFT).getUsed()) {
            if (viewSlots.get(ViewPosition.BOTTOMLEFT).getUsed()) {
                leftPane.setDividerPositions(0.5);
                mainSplitPane.setDividerPosition(0, 0.3);
            }
            else {
                leftPane.setDividerPositions(1.0);
                mainSplitPane.setDividerPosition(0, 0.3);
            }
        }
        else if (viewSlots.get(ViewPosition.BOTTOMLEFT).getUsed()) {
            leftPane.setDividerPositions(0.0);
            mainSplitPane.setDividerPosition(0, 0.3);
        }

        if (viewSlots.get(ViewPosition.TOPRIGHT).getUsed()) {
            if (viewSlots.get(ViewPosition.BOTTOMRIGHT).getUsed()) {
                rightPane.setDividerPositions(0.5);
                mainSplitPane.setDividerPosition(1, 0.7);
            }
            else {
                rightPane.setDividerPositions(1.0);
                mainSplitPane.setDividerPosition(1, 0.7);
            }
        }
        else if (viewSlots.get(ViewPosition.BOTTOMRIGHT).getUsed()) {
            rightPane.setDividerPositions(0.0);
            mainSplitPane.setDividerPosition(1, 0.7);
        }
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
}
