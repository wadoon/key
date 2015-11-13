package de.uka.ilkd.key.nui;


import java.io.IOException;
import java.net.URL;

import de.uka.ilkd.key.nui.view.MainViewController;
import de.uka.ilkd.key.nui.view.RootLayoutController;
import de.uka.ilkd.key.nui.view.SequentViewController;
import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Scene;
import javafx.scene.image.Image;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;

public class MainApp extends Application {

    private Stage primaryStage;
    private BorderPane rootLayout;
    private RootLayoutController rootLayoutController;

    @Override
    public void start(Stage primaryStage) {
        this.primaryStage = primaryStage;
        this.primaryStage.setTitle("KeY Project");

        // Set the application icon.
        this.primaryStage.getIcons().add(new Image("file:resources/images/key-color-icon-square.png"));

        initRootLayout();
        registerViews();
        primaryStage.show();
    }

    /**
     * Initializes the root layout.
     */
    public void initRootLayout() {
        try {
            // Load root layout from fxml file.
            FXMLLoader loader = new FXMLLoader();
            loader.setLocation(MainApp.class.getResource("view/RootLayout.fxml"));
            rootLayout = (BorderPane) loader.load();

            // Show the scene containing the root layout.
            Scene scene = new Scene(rootLayout);
            primaryStage.setScene(scene);

            // Give the controller access to the main app.
            RootLayoutController controller = loader.getController();
            controller.setMainApp(this);
            rootLayoutController = controller;
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Shows the Main View inside the root layout.

    public void showMainView() {
        try {
            // Load main view
            FXMLLoader loader = new FXMLLoader();
            loader.setLocation(MainApp.class.getResource("view/MainView.fxml"));
            AnchorPane mainView = (AnchorPane) loader.load();

            // Set main view into the center of root layout.
            rootLayout.setCenter(mainView);

            // Give the controller access to the main app.
            MainViewController controller = loader.getController();
            controller.setMainApp(this);

        } catch (IOException e) {
            e.printStackTrace();
        }
    }*/

    /**
     * Shows the SequentView inside the root layout.

    public void showSequentView() {
        try {
            // Load Sequent view
            FXMLLoader loader = new FXMLLoader();
            loader.setLocation(MainApp.class.getResource("view/SequentView.fxml"));
            AnchorPane mainView = (AnchorPane) loader.load();

            // Set sequent view into the center of root layout.
            rootLayout.setCenter(mainView);

            // Give the controller access to the main app.
            SequentViewController controller = loader.getController();
            controller.setMainApp(this);

        } catch (IOException e) {
            e.printStackTrace();
        }
    }*/

    private void registerViews(){
        rootLayoutController.registerView("Sequent", MainApp.class.getResource("view/SequentView.fxml"));
        rootLayoutController.registerView("Main", MainApp.class.getResource("view/MainView.fxml"));
    }

    /**
     * Returns the main stage.
     * @return
     */
    public Stage getPrimaryStage() {
        return primaryStage;
    }

    public static void main(String[] args) {
        launch(args);
    }
}