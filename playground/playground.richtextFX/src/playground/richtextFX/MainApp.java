package playground.richtextFX;

import java.io.File;
import java.net.URL;
import java.util.Set;

import org.reflections.Reflections;

import de.uka.ilkd.key.proof.Proof;
import javafx.application.Application;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.image.Image;
import javafx.scene.layout.BorderPane;
import javafx.stage.Popup;
import javafx.stage.Stage;
import playground.richtextFX.view.RootLayoutController;

public class MainApp extends Application {

    private Stage primaryStage;
    private BorderPane rootLayout;
    private RootLayoutController rootLayoutController;
    private Reflections reflections = new Reflections("playground.richtextFX");
    private Popup popup = new Popup();
    private Label popupMsg = new Label();
    @Override
    public void start(Stage primaryStage) {
        this.primaryStage = primaryStage;
        this.primaryStage.setTitle("KeY Project");

        // Set the application icon.
        this.primaryStage.getIcons().add(
                new Image("file:resources/images/key-color-icon-square.png"));
        
        
        
        popupMsg.setStyle(
                "-fx-background-color: black;" +
                "-fx-text-fill: white;" +
                "-fx-padding: 5;");
        popup.getContent().add(popupMsg);

        initRootLayout();
        scanForViews();
        scanForMenus();
        primaryStage.show();
    }
    public void setPopUp(String s){
        popupMsg.setText(s);
    }
    public void showPopUp(Node node, double a, double b){
        popup.show(node, a, b);
    }
    public void hidePopUp(){
        popup.hide();
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
            Scene scene = new Scene(rootLayout);
            scene.widthProperty().addListener(new ChangeListener<Number>() {
                @Override
                public void changed(
                        ObservableValue<? extends Number> observableValue,
                        Number oldSceneWidth, Number newSceneWidth) {
                    ((RootLayoutController) loader.getController()).resize();
                }
            });
            scene.heightProperty().addListener(new ChangeListener<Number>() {
                @Override
                public void changed(
                        ObservableValue<? extends Number> observableValue,
                        Number oldSceneHeight, Number newSceneHeight) {
                    ((RootLayoutController) loader.getController()).resize();
                }
            });
            primaryStage.setScene(scene);

            // Give the controller access to the main app.
            RootLayoutController controller = loader.getController();
            controller.setMainApp(this);
            rootLayoutController = controller;
        }
        catch (Exception e) {
            e.printStackTrace();
        }
    }

    private void scanForViews() {
        Set<Class<?>> annotated = reflections
                .getTypesAnnotatedWith(KeYView.class);
        for (Class<?> c : annotated) {
            KeYView annot = c.getAnnotation(KeYView.class);
            // no used yet
            // if (Arrays.asList(annot.windows()).contains("Main"))
            rootLayoutController.registerView(annot.title(),
                    c.getResource(annot.path()), annot.preferredPosition(),
                    annot.accelerator());
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

    public Proof getProof() {
        return rootLayoutController.getProof();
    }
    public void setProof(File file) {
        rootLayoutController.setProof(file);
    }
    public void setStatus(String status) {
        rootLayoutController.setStatus(status);
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