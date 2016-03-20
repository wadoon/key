package de.uka.ilkd.key.nui;

import java.net.URL;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.prefs.BackingStoreException;
import java.util.prefs.Preferences;

import org.reflections.Reflections;

import de.uka.ilkd.key.nui.view.RootLayoutController;
import de.uka.ilkd.key.nui.util.KeyFxmlLoader;
import de.uka.ilkd.key.nui.util.NUIConstants;
import de.uka.ilkd.key.nui.util.SerializableViewInformation;
import de.uka.ilkd.key.util.KeYResourceManager;
import javafx.application.Application;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.image.Image;
import javafx.scene.layout.BorderPane;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.util.Pair;

public class MainApp extends Application {

    private static boolean isDebugView = false;

    public static boolean isDebugView() {
        return isDebugView;
    }

    private Stage primaryStage;
    private BorderPane rootLayout;
    private RootLayoutController rootLayoutController;
    /**
     * the string specifies the prefix for packages that should be scanned for
     * annotations
     */
    private Reflections reflections = new Reflections("de.uka.ilkd.key");
    private Scene scene;
    boolean ctrlPressed = false;

    @Override
    public void start(Stage primaryStage) {
        this.primaryStage = primaryStage;
        this.primaryStage.setTitle(
                KeYResourceManager.getManager().getUserInterfaceTitle());

        // Set the application icon.
        this.primaryStage.getIcons()
                .add(new Image(NUIConstants.KEY_WINDOW_ICON));

        SessionSettings settings = SessionSettings.loadLastSettings();
        boolean useBoundsSettings = settings != null
                && !settings.getBoundsIsCorrupted();
        Map<String, SerializableViewInformation> viewmap = new HashMap<>();
        if (useBoundsSettings) {
            primaryStage.setX(settings.getWindowX());
            primaryStage.setY(settings.getWindowY());
            primaryStage.setWidth(settings.getWindowWidth());
            primaryStage.setHeight(settings.getWindowHeight());
        }
        else
            System.out.println(
                    "Gui bound settings are corrupted - using default");
        if (settings != null) {
            for (SerializableViewInformation sv : settings.getViews()) {
                viewmap.put(sv.getFxmlUrl(), sv);
            }
        }
        initRootLayout();

        setCtrlPressedHandler();
        setCloseWindowConfirmHandler();
        scanForViews(useBoundsSettings ? viewmap : new HashMap<>());
        scanForMenus();

        primaryStage.show();

        if (useBoundsSettings) {
            rootLayoutController
                    .setSplitterPositions(settings.getSplitterPositions());
        }
    }

    /**
     * Initializes the root layout.
     */
    public void initRootLayout() {
        try {
            // Load root layout from fxml file.
            FXMLLoader loader = new FXMLLoader();
            URL path = MainApp.class.getResource("view/RootLayout.fxml");
            if (path == null)
                throw new RuntimeException("Could not find RootLayout.fxml");
            loader.setLocation(path);
            rootLayout = (BorderPane) loader.load();

            // Show the scene containing the root layout.
            scene = new Scene(rootLayout);
            scene.getStylesheets()
                    .add("file:resources/css/themes/DefaultTheme.css");

            rootLayout.prefHeightProperty().bind(scene.heightProperty());

            scene.widthProperty().addListener(
                    (observableValue, oldSceneWidth, newSceneWidth) -> {
                        ((RootLayoutController) loader.getController())
                                .resize();
                    });

            scene.heightProperty().addListener(
                    (observableValue, oldSceneHeight, newSceneHeight) -> {
                        ((RootLayoutController) loader.getController())
                                .resize();
                    });

            primaryStage.setScene(scene);

            // Give the controller access to the main app.
            RootLayoutController controller = loader.getController();
            controller.setMainApp(this, new Context(this));
            rootLayoutController = controller;
        }
        catch (Exception e) {
            e.printStackTrace();
        }
    }

    public RootLayoutController getRootLayoutController() {
        return rootLayoutController;
    }

    /**
     * Opens a new window and shows the view specified by given FXML in it. The
     * CSS applied to the main window will also be applied to the new window.
     * 
     * @param title
     *            the window title
     * @param fxmlPath
     *            the path to the FXML
     * @param resizable
     *            if the window should be resizable
     * @param blockParent
     *            if access to the main window should be blocked
     * @param additionalStylesheets
     *            ObservableList containing Strings of paths to additional CSS.
     * @return the controller for the FXML
     */
    public ViewController openNewWindow(String title, String fxmlPath,
            boolean resizable, boolean blockParent) {
        return openNewWindow(title, fxmlPath, resizable, blockParent,
                FXCollections.emptyObservableList());
    }

    /**
     * Opens a new window and shows the view specified by given FXML in it. The
     * CSS applied to the main window will also be applied to the new window.
     * 
     * @param title
     *            the window title
     * @param fxmlPath
     *            the path to the FXML
     * @param resizable
     *            if the window should be resizable
     * @param blockParent
     *            if access to the main window should be blocked
     * @param additionalStylesheets
     *            ObservableList containing Strings of paths to additional CSS.
     * @return the controller for the FXML
     */
    public ViewController openNewWindow(String title, String fxmlPath,
            boolean resizable, boolean blockParent,
            ObservableList<String> additionalStylesheets) {
        Stage stage = new Stage();
        stage.setTitle(title);
        stage.getIcons().add(new Image(NUIConstants.KEY_WINDOW_ICON));

        if (blockParent)
            stage.initModality(Modality.WINDOW_MODAL);
        stage.initOwner(scene.getWindow());

        Pair<Object, Object> p = KeyFxmlLoader
                .loadFxml(MainApp.class.getResource(fxmlPath));
        stage.setScene(new Scene((Parent) p.getKey()));
        stage.show();

        stage.getScene().getStylesheets().addAll(scene.getStylesheets());
        stage.getScene().getStylesheets().addAll(additionalStylesheets);
        stage.setResizable(resizable);

        ((ViewController) p.getValue()).setStage(stage);
        ((ViewController) p.getValue()).setMainApp(this,
                rootLayoutController.getContext());
        return (ViewController) p.getValue();
    }

    /**
     * Listens for ControlDown Event.
     */
    private void setCtrlPressedHandler() {
        scene.setOnKeyPressed((value) -> {
            if (value.isControlDown())
                ctrlPressed = true;
        });
        scene.setOnKeyReleased((value) -> {
            ctrlPressed = false;
        });
    }

    /**
     * Listens for a Window Close Request and prompts the user to confirm. Skips
     * the dialog if ctrl is pressed while closing.
     */
    private void setCloseWindowConfirmHandler() {
        scene.getWindow().setOnCloseRequest((event) -> {
            if (!ctrlPressed) {
                closeWindowAlert();
                event.consume();
            }
            else {
                saveAndClose();
            }
        });
    }

    /**
     * Alert that pops up when trying to close the application.
     */
    public void closeWindowAlert() {
        Alert alert = new Alert(AlertType.CONFIRMATION);
        alert.setTitle("Close KeY");
        alert.setHeaderText(null);
        alert.setContentText("Really quit?");
        // Get the Stage.
        Stage stage = (Stage) alert.getDialogPane().getScene().getWindow();

        // Add a custom icon.
        stage.getIcons().add(new Image(NUIConstants.KEY_WINDOW_ICON));

        Optional<ButtonType> result = alert.showAndWait();
        if (result.get() != ButtonType.OK)
            return;

        saveAndClose();
    }

    /**
     * Saves window settings and closes the main stage.
     */
    private void saveAndClose() {
        SessionSettings settings = new SessionSettings();
        settings.setWindowX(primaryStage.getX());
        settings.setWindowY(primaryStage.getY());
        settings.setWindowHeight(primaryStage.getHeight());
        settings.setWindowWidth(primaryStage.getWidth());
        settings.setSplitterPositions(
                rootLayoutController.getSplitterPositions());
        settings.setViews(rootLayoutController.getViewInformations());
        settings.saveAsLast();
        System.out.println("Where we go from here is a choice I leave to you.");
        primaryStage.close();
    }

    private void scanForViews(
            Map<String, SerializableViewInformation> lastViewPositions) {
        ViewObserver rootViewObserver = new ViewObserver(rootLayoutController);
        Set<Class<?>> annotated = reflections
                .getTypesAnnotatedWith(KeYView.class);
        for (Class<?> c : annotated) {
            KeYView annot = c.getAnnotation(KeYView.class);

            URL fxmlUrl = c.getResource(annot.path());
            ViewPosition pos = annot.preferredPosition();
            SerializableViewInformation sv = lastViewPositions
                    .containsKey(fxmlUrl.getPath())
                            ? lastViewPositions.get(fxmlUrl.getPath()) : null;
            if (sv != null) {
                pos = sv.getViewPosition();
            }
            ViewInformation info = new ViewInformation(annot.title(), fxmlUrl,
                    pos, annot.hasMenuItem());
            info.addObserver(rootViewObserver);
            rootLayoutController.registerView(info, annot.accelerator());
            if (sv != null)
                info.setIsActive(sv.getIsActibe());
            else
                info.setIsActive(annot.defaultActive());
        }
    }

    private void scanForMenus() {
        Set<Class<?>> annotated = reflections
                .getTypesAnnotatedWith(KeYMenu.class);
        for (Class<?> c : annotated) {
            KeYMenu annot = c.getAnnotation(KeYMenu.class);
            // not used yet
            // if (Arrays.asList(annot.windows()).contains("Main")) {
            if (annot.parentMenu().equals("")) {
                rootLayoutController.registerMenu(c.getResource(annot.path()));
            }
            else {
                rootLayoutController.registerMenuEntry(
                        c.getResource(annot.path()), annot.parentMenu());
            }
            // }
        }
    }

    /**
     * Returns the main stage.
     * 
     * @return
     */
    public Stage getPrimaryStage() {
        return primaryStage;
    }

    public static void main(String[] args) {
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
            case "debug":
                isDebugView = true;
                break;
            case "reset":
                System.out.println("'reset' paramter found -> resetting preferences");
                Preferences prefs = Preferences
                .userNodeForPackage(SessionSettings.class);
                try {
                    prefs.clear();
                }
                catch (BackingStoreException e) {
                    e.printStackTrace();
                }
                break;
            default:
                break;
            }
        }
        launch(args);
    }
}