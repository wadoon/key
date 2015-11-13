/**
 * 
 */
package de.uka.ilkd.key.nui.view;

import java.io.IOException;
import java.net.URL;
import java.util.LinkedList;

import de.uka.ilkd.key.nui.IViewContainer;
import de.uka.ilkd.key.nui.MainApp;
import de.uka.ilkd.key.nui.ViewController;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.input.KeyCombination;
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;

/**
 * @author Maximilian Li
 *
 */
public class RootLayoutController extends ViewController implements IViewContainer {

    private static final int MaxMenuEntries = 8;

    /**
     * The BorderPane from the Main Window
     */
    @FXML
    BorderPane mainPane;

    /**
     * Opens a new Window with About Functionality. View: AboutView.fxml
     * @param event ActionEvent
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

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Closes the program on Click
     */
    @FXML
    private void handleClose() {
        System.exit(0);
    }

    /**
     * 
     */
    public RootLayoutController() {
        // TODO Auto-generated constructor stub
    }

    @FXML
    private Menu registeredViewsMenu;
    
    private Menu otherViews = null;

    public void registerView(String title,URL path, KeyCombination keys){
        MenuItem item = new MenuItem();
        item.setText(title);
        item.setOnAction(e -> showView(path)); 

        if(keys != null)
            item.setAccelerator(keys);
        
        if(registeredViewsMenu.getItems().size() < MaxMenuEntries) {
            registeredViewsMenu.getItems().add(item);
        }
        else{
            if(otherViews == null){
                otherViews = new Menu("Other");
                registeredViewsMenu.getItems().add(otherViews);
            }
            otherViews.getItems().add(item);
        }
    } 

    public void registerView(String title, URL path) {
       registerView(title,path,null);
    }
    
    private void showView(URL path) {
        try {
            // Load main view
            FXMLLoader loader = new FXMLLoader();
            loader.setLocation(path);
            
            mainPane.setCenter(loader.load());
            
            // Give the controller access to the main app.
            ViewController controller = loader.getController();
            controller.setMainApp(mainApp);
            
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
