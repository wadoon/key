/**
 * 
 */
package de.uka.ilkd.key.nui.view;

import java.io.IOException;
import java.net.URL;

import de.uka.ilkd.key.nui.IViewContainer;
import de.uka.ilkd.key.nui.MainApp;
import de.uka.ilkd.key.nui.ViewController;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Scene;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SplitPane;
import javafx.scene.input.KeyCombination;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;

/**
 * @author Maximilian Li
 *
 */
public class RootLayoutController extends ViewController implements IViewContainer {

    private static final int MaxMenuEntries = 8;
    private final String main = "MAIN";
    private final String topLeft = "TOPLEFT";
    private final String bottomLeft = "BOTTOMLEFT";
    private final String topRight = "TOPRIGHT";
    private final String bottomRight = "BOTTOMRIGHT";

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

    private Menu otherViewsMenu = null;

    public void registerView(String title,URL path, String prefLoc, KeyCombination keys){
        MenuItem item = new MenuItem();
        item.setText(title);
        item.setOnAction(e -> showView(path, prefLoc)); 

        if(keys != null)
            item.setAccelerator(keys);

        if(registeredViewsMenu.getItems().size() < MaxMenuEntries) {
            registeredViewsMenu.getItems().add(item);
        }
        else{
            if(otherViewsMenu == null){
                otherViewsMenu = new Menu("Other");
                registeredViewsMenu.getItems().add(otherViewsMenu);
            }
            otherViewsMenu.getItems().add(item);
        }
    } 

    public void registerView(String title, URL path, String prefLoc) {
        registerView(title,path,prefLoc,null);
    }

    private void showView(URL path, String prefLoc) {
    	switch (prefLoc) {
		case main:
			mainPane.setCenter(loadFxml(path));
			break;
		case topLeft:
			AnchorPane view = (AnchorPane) loadFxml(path);
			SplitPane left = (SplitPane) mainPane.getLeft();
            AnchorPane ancTopLeft = (AnchorPane) left.getItems().get(0);
            ancTopLeft.setTopAnchor(view, 0.0);
            ancTopLeft.getChildren().add(view);
            left.setPrefWidth(200.0);
            break;
		default:
			mainPane.setCenter(loadFxml(path));
			break;
		}
    }

    @FXML
    private MenuBar menuBar;

    @FXML
    private Menu helpMenu;

    public void registerMenu(URL sourcePath){
        // add additional menus right before the "Help" entry
        menuBar.getMenus().add(menuBar.getMenus().indexOf(helpMenu),loadFxml(sourcePath));
    }
/*
    public enum MainMenus{
        File,
        Views,
        Help
    }

    public void registerSubMenu(MainMenus menu,URL sourcePath){
        // add additional menus right before the "Help" entry
        menuBar.getMenus().add(menuBar.getMenus().indexOf(helpMenu),loadFxml(sourcePath));
    }
*/

    private <T> T loadFxml(URL path){
        try {
            // Load main view
            FXMLLoader loader = new FXMLLoader();
            loader.setLocation(path);

            T content = loader.load();

            // Give the controller access to the main app.
            ViewController controller = loader.getController();
            controller.setMainApp(mainApp);

            return content;

        } catch (IOException e) {
            e.printStackTrace();
            return null;
        }
    }

}
