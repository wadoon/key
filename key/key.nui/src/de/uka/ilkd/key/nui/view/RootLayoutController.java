/**
 * 
 */
package de.uka.ilkd.key.nui.view;

import java.io.IOException;
import java.net.URL;

import de.uka.ilkd.key.nui.IViewContainer;
import de.uka.ilkd.key.nui.MainApp;
import de.uka.ilkd.key.nui.ViewController;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Scene;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
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
    
    /**
     * Constants for positioning
     */
    private final int centerPos = 0;
    private final int topLeftPos = 1;
    private final int bottomLeftPos = 2;
    private final int topRightPos = 3;
    private final int bottomRightPos = 4;
    
    /**
     * Checks for keeping track of used AnchorPane
     */
    private boolean centerUsed = false;
    private boolean topLeftUsed = false;
    private boolean bottomLeftUsed = false;
    private boolean topRightUsed = false;
    private boolean bottomRightUsed = false;

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
    AnchorPane topLeft;
    @FXML
    AnchorPane bottomLeft;
    @FXML
    AnchorPane center;
    @FXML
    AnchorPane topRight;
    @FXML
    AnchorPane bottomRight;

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

    public void registerView(String title,URL path, int prefLoc, KeyCombination keys){
    	CheckMenuItem item = new CheckMenuItem();
        item.setText(title); 
        item.selectedProperty().addListener(new ChangeListener<Boolean>() {
        	public void  changed(ObservableValue<? extends Boolean> ov, Boolean oldValue, Boolean newValue){
        		if (newValue){
        			showView(path, prefLoc);
        		} else {
        			clearView(prefLoc);
        		}
        		resize();
        	}
		});
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

    public void registerView(String title, URL path, int prefLoc) {
        registerView(title,path,prefLoc,null);
    }

    private void showView(URL path, int prefLoc) {
    	AnchorPane position;
    	AnchorPane view = (AnchorPane) loadFxml(path);
    	
    	int leftElements = leftPane.getChildrenUnmodifiable().size();
    	int rightElements = rightPane.getChildrenUnmodifiable().size();
    	
    	switch (prefLoc) {
		case centerPos:
			position = center;
			centerUsed = true;
			break;
		case topLeftPos:
			position = topLeft;
			topLeftUsed = true;
            break;
		case bottomLeftPos:
			position = bottomLeft;
			bottomLeftUsed = true;
			break;
		case topRightPos:
			position = topRight;
			topRightUsed = true;
			break;
		case bottomRightPos:
			position = bottomRight;
			bottomRightUsed = true;
			break;
		default:
			position = center;
			centerUsed = true;
			break;
		}
    	position.setTopAnchor(view, 0.0);
    	position.getChildren().clear();
    	position.getChildren().add(view);
    }
    
    private void clearView(int prefLoc){
    	AnchorPane position;
    	switch (prefLoc){
    	case centerPos:
			position = center;
			centerUsed = false;
			break;
		case topLeftPos:
			position = topLeft;
			topLeftUsed = false;
            break;
		case bottomLeftPos:
			position = bottomLeft;
			bottomLeftUsed = false;
			break;
		case topRightPos:
			position = topRight;
			topRightUsed = false;
			break;
		case bottomRightPos:
			position = bottomRight;
			bottomRightUsed = false;
			break;
		default:
			position = center;
			centerUsed = false;
			break;
		}
    	position.getChildren().clear();
    }
    
    private void resize(){
    	mainSplitPane.setDividerPositions(0.0, 1.0);
    	if (topLeftUsed){
    		if (bottomLeftUsed){
    			leftPane.setDividerPositions(0.5);
    			mainSplitPane.setDividerPosition(0, 0.3);
    		} else{
    			leftPane.setDividerPositions(1.0);
    			mainSplitPane.setDividerPosition(0, 0.3);
    		}
    	} else if (bottomLeftUsed){
    		leftPane.setDividerPositions(0.0);
			mainSplitPane.setDividerPosition(0, 0.3);
    	}
    	
    	if (topRightUsed){
    		if (bottomRightUsed){
    			rightPane.setDividerPositions(0.5);
    			mainSplitPane.setDividerPosition(0, 0.7);
    		} else{
    			rightPane.setDividerPositions(1.0);
    			mainSplitPane.setDividerPosition(0, 0.7);
    		}
    	} else if (bottomRightUsed){
    		rightPane.setDividerPositions(0.0);
			mainSplitPane.setDividerPosition(0, 0.7);
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
    
    public void registerMenuEntry(URL sourcePath,String parentMenu) throws IllegalStateException{
        for(Menu m : menuBar.getMenus()){
            if(m.getText() == parentMenu){
                m.getItems().add(loadFxml(sourcePath));
                return;
            }
        }
        throw new IllegalStateException("Menu " + parentMenu + " was not found");
    }

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
