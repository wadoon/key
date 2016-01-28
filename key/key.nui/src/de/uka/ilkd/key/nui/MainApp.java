package de.uka.ilkd.key.nui;

import java.net.URL;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import org.reflections.Reflections;

import de.uka.ilkd.key.nui.model.Context;
import de.uka.ilkd.key.nui.model.SessionSettings;
import de.uka.ilkd.key.nui.model.ViewInformation;
import de.uka.ilkd.key.nui.view.RootLayoutController;
import de.uka.ilkd.key.nui.util.SerializableViewInformation;
import de.uka.ilkd.key.util.KeYResourceManager;
import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.image.Image;
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;

public class MainApp extends Application {

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
        this.primaryStage.setTitle(KeYResourceManager.getManager().getUserInterfaceTitle());

        // Set the application icon.
        this.primaryStage.getIcons().add(
                new Image("file:resources/images/key-color-icon-square.png"));

        SessionSettings settings = SessionSettings.loadLastSettings();
        boolean useSettings = settings != null && !settings.getIsCorrupted();
        Map<String, SerializableViewInformation> viewmap = new HashMap<>();
        if (useSettings) {
            primaryStage.setX(settings.getWindowX());
            primaryStage.setY(settings.getWindowY());
            primaryStage.setWidth(settings.getWindowWidth());
            primaryStage.setHeight(settings.getWindowHeight());
            for (SerializableViewInformation sv : settings.getViews()) {
                viewmap.put(sv.getFxmlUrl(), sv);
            }
        }
        initRootLayout();

        ctrlPressedHandler();
        closeWindowConfirmHandler();
        scanForViews(useSettings ? viewmap : new HashMap<>());
        scanForMenus();

        primaryStage.show();
        
        if (useSettings)
            rootLayoutController
                    .setSplitterPositions(settings.getSplitterPositions());
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

            rootLayout.prefHeightProperty().bind(scene.heightProperty());

            scene.widthProperty().addListener(
                    (observableValue, oldSceneWidth, newSceneWidth) -> {
                        ((RootLayoutController) loader.getController())
                                .resize();
                    });
            /*
             * scene.heightProperty().addListener((observableValue,
             * oldSceneHeight, newSceneHeight) -> { ((RootLayoutController)
             * loader.getController()).resize(); });
             */

            primaryStage.setScene(scene);

            // Give the controller access to the main app.
            RootLayoutController controller = loader.getController();
            Context rootContext = new Context();
            rootContext.setStatusManager(controller);
            controller.setMainApp(this, rootContext);
            rootLayoutController = controller;
        }
        catch (Exception e) {
            e.printStackTrace();
        }
    }

    /**
     * Listens for ControlDown Event.
     */
    private void ctrlPressedHandler() {
        scene.setOnKeyPressed((value) -> {
            if (value.isControlDown())
                ctrlPressed = true;
        });
        scene.setOnKeyReleased((value) -> {
            ctrlPressed = false;
        });
    }

    /**
     * Listens for a Window Close Request and prompts the user to confirm.
     */
    private void closeWindowConfirmHandler() {
        scene.getWindow().setOnCloseRequest((event) -> {
            if (!ctrlPressed) {
                closeWindowAlert();
                event.consume();
            }
            else {
                primaryStage.close();
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
        stage.getIcons().add(
                new Image("file:resources/images/key-color-icon-square.png"));

        Optional<ButtonType> result = alert.showAndWait();
        if (result.get() != ButtonType.OK)
            return;

        SessionSettings settings = new SessionSettings();
        settings.setWindowX(primaryStage.getX());
        settings.setWindowY(primaryStage.getY());
        settings.setWindowHeight(primaryStage.getHeight());
        settings.setWindowWidth(primaryStage.getWidth());
        settings.setSplitterPositions(
                rootLayoutController.getSplitterPositions());
        settings.setViews(rootLayoutController.getViewInformations());
        settings.SaveAsLast();
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
                    .containsKey(fxmlUrl.getPath()) ? lastViewPositions.get(fxmlUrl.getPath()) : null;
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
                info.setIsActive(true);
        }
        System.out.println("Views: " + annotated.size());
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
        System.out.println("Menus: " + annotated.size());
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
        launch(args);
    }
}