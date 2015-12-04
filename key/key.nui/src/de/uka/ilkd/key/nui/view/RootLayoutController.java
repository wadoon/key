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

import de.uka.ilkd.key.model.ProofManager;
import de.uka.ilkd.key.model.ViewInformation;
import de.uka.ilkd.key.nui.MainApp;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.view.menu.ViewContextMenuController;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.event.ActionEvent;
import javafx.event.Event;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.geometry.Side;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SplitPane;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.input.ClipboardContent;
import javafx.scene.input.DragEvent;
import javafx.scene.input.Dragboard;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.MouseButton;
import javafx.scene.input.MouseEvent;
import javafx.scene.input.TransferMode;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Pane;
import javafx.stage.FileChooser;
import javafx.stage.FileChooser.ExtensionFilter;
import javafx.stage.Stage;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 *
 */
public class RootLayoutController extends ViewController {

    private static final int MaxMenuEntries = 8;

    private ProofManager proofManager = new ProofManager();

    @FXML
    private Label statusLabel;

    private final HashMap<ViewPosition, BorderPane> positionMapping;
    private final HashMap<ViewPosition, Boolean> positionUsage;
    private final HashMap<String, Tab> viewTabs;
    private final HashMap<String, ViewInformation> views;
    private Tab dragTab;

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

    public RootLayoutController() {
        positionUsage = new HashMap<ViewPosition, Boolean>();
        positionUsage.put(ViewPosition.BOTTOMLEFT, false);
        positionUsage.put(ViewPosition.BOTTOMRIGHT, false);
        positionUsage.put(ViewPosition.CENTER, false);
        positionUsage.put(ViewPosition.TOPLEFT, false);
        positionUsage.put(ViewPosition.TOPRIGHT, false);

        positionMapping = new HashMap<>();
        viewTabs = new HashMap<>();
        views = new HashMap<>();
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        positionMapping.put(ViewPosition.BOTTOMLEFT, bottomLeft);
        positionMapping.put(ViewPosition.BOTTOMRIGHT, bottomRight);
        positionMapping.put(ViewPosition.CENTER, center);
        positionMapping.put(ViewPosition.TOPLEFT, topLeft);
        positionMapping.put(ViewPosition.TOPRIGHT, topRight);

        positionMapping.forEach((k, v) -> {
            v.setCenter(new TabPane());
            registerDragListeners(v.getCenter());
        });

        // Load a standard proof when starting the program for testing purposes
        // TODO Remove then following 3 lines and folder "resources/proofs" at
        // end of project or when not needed anymore
        // File file = new File("resources/proofs/gcd.closed.proof");
        // proof = loadProof(file);
        // statusLabel.setText("Proof loaded: " + file.getName());
    }

    /**
     * Adds Drag&Drop acceptance to Pane
     * 
     * @param node
     */
    private void registerDragListeners(Node node) {
        node.setOnDragOver(new EventHandler<DragEvent>() {
            public void handle(DragEvent event) {
                if (event.getGestureSource() != node) {
                    event.acceptTransferModes(TransferMode.MOVE);
                }
                event.consume();
            }
        });
        node.setOnDragEntered(new EventHandler<DragEvent>() {
            public void handle(DragEvent event) {
                if (event.getGestureSource() != node) {
                    System.out.println("valid target entered");
                    // node.setEffect(new Glow());
                    node.setStyle(
                            "-fx-padding: 1; -fx-background-color: yellow, -fx-control-inner-background; -fx-background-insets: 0, 1;");
                }
                event.consume();
            }
        });
        node.setOnDragExited(new EventHandler<DragEvent>() {
            public void handle(DragEvent event) {
                System.out.println("target exited");
                // node.setEffect(null);
                node.setStyle("");
                event.consume();
            }
        });
        node.setOnDragDropped(new EventHandler<DragEvent>() {
            public void handle(DragEvent event) {
                boolean success = false;
                if (dragTab != null) {
                    views.get(dragTab.getText()).setCurrentPosition(getTabPosition(node));
                    dragTab = null;
                    success = true;
                }
                event.setDropCompleted(success);
                event.consume();
            }
        });
    }

    /**
     * Opens a new Window with About Functionality. View: AboutView.fxml
     * 
     * @param event
     *            ActionEvent
     */
    @FXML
    private void handleAbout(ActionEvent event) {
        System.out.println("About clicked");

        try {
            FXMLLoader loader = new FXMLLoader();
            loader.setLocation(MainApp.class.getResource("view/AboutView.fxml"));

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
        mainApp.closeWindowAlert();
    }

    /**
     * Opens a file chooser to choose a proof to be loaded.
     */
    @FXML
    private void handleOpen() {
        setStatus("Loading Proof...");
        FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle("Select a proof to load");
        fileChooser.getExtensionFilters().addAll(new ExtensionFilter("Proofs", "*.proof"),
                new ExtensionFilter("All Files", "*.*"));
        fileChooser.setInitialDirectory(new File("../"));

        File file = fileChooser.showOpenDialog(new Stage());

        if (file == null) {
            setStatus("No File Selected");
            return;
        }

        proofManager.setMainApp(mainApp);
        proofManager.setProof(file);
    }

    /**
     * Set a status in the status bar.
     * 
     * @param status
     *            Status to be set.
     */
    public void setStatus(String status) {
        statusLabel.setText(status);
    }

    public void clearStatus() {
        setStatus("");
    }

    /**
     * Enable/Disable Pretty Syntax
     */
    @FXML
    private void handlePrettySyntax() {
        // TODO implement functionality
    }

    @FXML
    private Menu viewsMenu;

    private Menu otherViewsMenu = null;

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

    public void registerView(ViewInformation info, String accelerator) {
        if (views.containsKey(info.getTitle()))
            throw new RuntimeException("Multiple views with the same name");

        views.put(info.getTitle(), info);
        CheckMenuItem item = new CheckMenuItem();
        item.setText(info.getTitle());
        item.selectedProperty().addListener(new ChangeListener<Boolean>() {
            public void changed(ObservableValue<? extends Boolean> ov, Boolean oldValue, Boolean newValue) {
                info.setIsActive(newValue);
                resize();
            }
        });
        item.setSelected(info.getIsActive());
        if (!accelerator.equals(""))
            item.setAccelerator(KeyCombination.valueOf(accelerator));

        // make overflow menu "Others" if items exceed max
        if (viewsMenu.getItems().size() < MaxMenuEntries) {
            viewsMenu.getItems().add(item);
        }
        else {
            if (otherViewsMenu == null) {
                otherViewsMenu = new Menu("Other");
                viewsMenu.getItems().add(otherViewsMenu);
            }
            otherViewsMenu.getItems().add(item);
        }
        
        //dummy until last opened or config was developed
        info.setIsActive(true);
    }

    public void showView(ViewInformation view) {
        Pane pane = (Pane) loadFxml(view.getFxmlPath());
        Tab tab;
        // check if tab was already created
        if (viewTabs.containsKey(view.getTitle())) {
            tab = viewTabs.get(view.getTitle());
        }
        else {
            tab = createTab(view, pane);
            viewTabs.put(view.getTitle(), tab);
        }
        setPosition(view.getTitle(), view.getPreferedPosition());
    }

    /**
     * 
     * @param title
     * @param node
     * @return a tab with content node and title as lable, also drag
     *         functionality
     */
    private Tab createTab(ViewInformation view, Node node) {
        Tab t = new Tab();
        Label l = new Label(view.getTitle());
        t.setGraphic(l);
        t.setContent(node);

        l.setOnDragDetected(new EventHandler<MouseEvent>() {
            public void handle(MouseEvent event) {
                Dragboard db = l.startDragAndDrop(TransferMode.MOVE);

                ClipboardContent content = new ClipboardContent();
                content.putString(view.getTitle());
                db.setContent(content);
                dragTab = t;
                event.consume();
            }
        });

        t.setOnCloseRequest(new EventHandler<Event>() {
            public void handle(Event event) {
                view.setIsActive(false);
            }
        });
        l.setOnMouseClicked((event) -> {
            if (event.getButton() == MouseButton.SECONDARY)
                loadViewContextMenu(view).show(l, Side.TOP, event.getX(), event.getY());
        });

        return t;
    }

    public void hideView(String title) {
        Tab tab = viewTabs.get(title);
        TabPane tabPane = tab.getTabPane();
        tabPane.getTabs().remove(tab);
        if (tabPane.getTabs().size() == 0) {
            // System.out.println(getViewPosition(tabPane.getParent()));
            positionUsage.put(getViewPosition(tabPane.getParent()), false);
        }
        resize();
    }

    public void moveView(String title, ViewPosition next) {
        hideView(title);
        setPosition(title, next);
    }

 /*   private Node getView(ViewPosition pos) {
        BorderPane container = positionMapping.get(pos);

        if (container != null && container.getChildren().size() == 1)
            return container.getChildren().get(0);
        else
            return null;
    }*/

    public ViewPosition getTabPosition(Node node) {
        for (ViewPosition key : positionMapping.keySet()) {
            // System.out.println(positionMapping.get(key));
            if (positionMapping.get(key).getChildren().size() == 1
                    && positionMapping.get(key).getChildren().get(0) == node)
                return key;
        }
        return null;
    }

    public ViewPosition getViewPosition(Node node) {
        for (ViewPosition key : positionMapping.keySet()) {
            // System.out.println(positionMapping.get(key));
            if (positionMapping.get(key) == node)
                return key;
        }
        return null;
    }

    private void setPosition(String title, ViewPosition position) {
        TabPane container = (TabPane) positionMapping.get(position).getCenter();
        container.getTabs().add(viewTabs.get(title));
        positionUsage.put(position, true);
        resize();
    }

    public void resize() {
        mainSplitPane.setDividerPositions(0.0, 1.0);
        if (positionUsage.get(ViewPosition.TOPLEFT)) {
            if (positionUsage.get(ViewPosition.BOTTOMLEFT)) {
                leftPane.setDividerPositions(0.5);
                mainSplitPane.setDividerPosition(0, 0.3);
            }
            else {
                leftPane.setDividerPositions(1.0);
                mainSplitPane.setDividerPosition(0, 0.3);
            }
        }
        else if (positionUsage.get(ViewPosition.BOTTOMLEFT)) {
            leftPane.setDividerPositions(0.0);
            mainSplitPane.setDividerPosition(0, 0.3);
        }

        if (positionUsage.get(ViewPosition.TOPRIGHT)) {
            if (positionUsage.get(ViewPosition.BOTTOMRIGHT)) {
                rightPane.setDividerPositions(0.5);
                mainSplitPane.setDividerPosition(1, 0.7);
            }
            else {
                rightPane.setDividerPositions(1.0);
                mainSplitPane.setDividerPosition(1, 0.7);
            }
        }
        else if (positionUsage.get(ViewPosition.BOTTOMRIGHT)) {
            rightPane.setDividerPositions(0.0);
            mainSplitPane.setDividerPosition(1, 0.7);
        }
    }

    public void registerMenu(URL sourcePath) {
        // add additional menus right before the "Help" entry
        menuBar.getMenus().add(menuBar.getMenus().indexOf(helpMenu), loadFxml(sourcePath));
    }

    public void registerMenuEntry(URL sourcePath, String parentMenu) throws IllegalStateException {
        for (Menu m : menuBar.getMenus()) {
            if (m.getText().equals(parentMenu)) {
                m.getItems().add(loadFxml(sourcePath));
                return;
            }
        }
        throw new IllegalStateException("Menu " + parentMenu + " was not found");
    }

    private ContextMenu loadViewContextMenu(ViewInformation view) {
        FXMLLoader loader = new FXMLLoader();
        loader.setLocation(ViewContextMenuController.class.getResource("ViewContextMenu.fxml"));
        ContextMenu content;
        try {
            content = loader.load();
        }
        catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
            return null;
        }

        // Give the controller access to the main app.
        ViewContextMenuController controller = loader.getController();
        controller.setMainApp(mainApp);
        controller.setParentView(view);
        content.setOnShowing((event) -> {
            // select current position
        });
        return content;
    }

    private <T> T loadFxml(URL path) {
        try {
            // Load main view
            FXMLLoader loader = new FXMLLoader();
            loader.setLocation(path);

            T content = loader.load();

            // Give the controller access to the main app.
            ViewController controller = loader.getController();
            controller.setMainApp(mainApp);

            return content;

        }
        catch (IOException e) {
            e.printStackTrace();
            return null;
        }
    }
}
