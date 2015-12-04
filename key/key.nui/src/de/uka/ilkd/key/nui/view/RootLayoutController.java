/**
 * 
 */
package de.uka.ilkd.key.nui.view;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.HashMap;
import java.util.Optional;
import java.util.ResourceBundle;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.IViewContainer;
import de.uka.ilkd.key.nui.MainApp;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.view.menu.ViewContextMenuController;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
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
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.ButtonType;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.control.SplitPane;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.image.Image;
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
public class RootLayoutController extends ViewController implements IViewContainer {

    private static final int MaxMenuEntries = 8;

    private Proof proof;

    @FXML
    private Label statusLabel;

    private final HashMap<ViewPosition, BorderPane> positionMapping;
    private final HashMap<ViewPosition, Boolean> positionUsage;

    private HashMap<URL, Tab> tabs;
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

        positionMapping = new HashMap<ViewPosition, BorderPane>();
        tabs = new HashMap<URL, Tab>();
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
                    moveView(dragTab, getTabPosition(node));
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
        Alert alert = new Alert(AlertType.CONFIRMATION);
        alert.setTitle("Close KeY");
        alert.setHeaderText(null);
        alert.setContentText("Really quit?");
        // Get the Stage.
        Stage stage = (Stage) alert.getDialogPane().getScene().getWindow();

        // Add a custom icon.
        stage.getIcons().add(new Image("file:resources/images/key-color-icon-square.png"));

        Optional<ButtonType> result = alert.showAndWait();
        if (result.get() == ButtonType.OK){
            System.exit(0);
        }
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

        setProof(file);
    }

    /**
     * Getter method for a proof.
     * 
     * @return The loaded Proof.
     */
    public Proof getProof() {
        return this.proof;
    }

    /**
     * Load a Proof.
     * 
     * @param file
     *            Proof to be loaded.
     */
    public void setProof(File file) {
        setStatus("Loading Proof...");
        proof = loadProof(file);
        setStatus("Proof loaded: " + file.getName());
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
    private Menu registeredViewsMenu;

    private Menu otherViewsMenu = null;

    public void registerView(String title, URL path, ViewPosition prefPos, String accelerator) {
        CheckMenuItem item = new CheckMenuItem();
        item.setText(title);
        item.selectedProperty().addListener(new ChangeListener<Boolean>() {
            public void changed(ObservableValue<? extends Boolean> ov, Boolean oldValue, Boolean newValue) {
                if (newValue) {
                    showView(title, path, prefPos);
                }
                else {
                    hideView(tabs.get(path));
                }
                resize();
            }
        });
        if (!positionUsage.get(prefPos))
            item.setSelected(true);
        if (!accelerator.equals(""))
            item.setAccelerator(KeyCombination.valueOf(accelerator));

        // make overflow menu "Others" if items exceed max
        if (registeredViewsMenu.getItems().size() < MaxMenuEntries) {
            registeredViewsMenu.getItems().add(item);
        }
        else {
            if (otherViewsMenu == null) {
                otherViewsMenu = new Menu("Other");
                registeredViewsMenu.getItems().add(otherViewsMenu);
            }
            otherViewsMenu.getItems().add(item);
        }
    }

    public void showView(String title, URL path, ViewPosition prefPos) {
        Pane view = (Pane) loadFxml(path);
        Tab tab = createTab(title, view);
        tabs.put(path, tab);
        tab.getGraphic().setOnMouseClicked((event) -> {
            if (event.getButton() == MouseButton.SECONDARY)
                loadViewContextMenu(tab).show(tab.getGraphic(), Side.TOP, event.getX(), event.getY());
        });
        setPosition(prefPos, tab);
    }

    /**
     * 
     * @param title
     * @param node
     * @return a tab with content node and title as lable, also drag
     *         functionality
     */
    private Tab createTab(String title, Node node) {
        Tab t = new Tab();
        Label l = new Label(title);
        t.setGraphic(l);
        t.setContent(node);

        l.setOnDragDetected(new EventHandler<MouseEvent>() {
            public void handle(MouseEvent event) {
                Dragboard db = l.startDragAndDrop(TransferMode.MOVE);

                ClipboardContent content = new ClipboardContent();
                content.putString(title);
                db.setContent(content);
                dragTab = t;
                event.consume();
            }
        });

        t.setOnClosed(new EventHandler<Event>() {
            public void handle(Event event) {
                // TODO handle
            }
        });

        return t;
    }

    public void hideView(Tab tab) {
        TabPane tabPane = tab.getTabPane();
        tabPane.getTabs().remove(tab);
        if (tabPane.getTabs().size() == 0) {
            // System.out.println(getViewPosition(tabPane.getParent()));
            positionUsage.put(getViewPosition(tabPane.getParent()), false);
        }

        resize();
    }

    public void moveView(Tab tab, ViewPosition next) {
        hideView(tab);
        setPosition(next, tab);
    }

    private Node getView(ViewPosition pos) {
        BorderPane container = positionMapping.get(pos);

        if (container != null && container.getChildren().size() == 1)
            return container.getChildren().get(0);
        else
            return null;
    }

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

    private void setPosition(ViewPosition pos, Tab tab) {
        TabPane container = (TabPane) positionMapping.get(pos).getCenter();
        container.getTabs().add(tab);
        positionUsage.put(pos, true);
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

    private ContextMenu loadViewContextMenu(Tab tab) {
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
        controller.setParentView(this, tab);
        content.setOnShowing((event) -> {
            // select current position
        });
        return content;
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof
     * is not null, and fails if the proof could not be loaded.
     *
     * @param proofFileName
     *            The file name of the proof file to load.
     * @return The loaded proof.
     */
    private Proof loadProof(File proofFile) {
        // File proofFile = new File("../" + proofFileName);

        try {
            KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null,
                    null, true);
            Proof proof = environment.getLoadedProof();

            return proof;
        }
        catch (ProblemLoaderException e) {
            e.printStackTrace();
            return null;
        }
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
