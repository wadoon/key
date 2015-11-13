/**
 * 
 */
package de.uka.ilkd.key.nui.view;

import java.io.IOException;

import de.uka.ilkd.key.nui.MainApp;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Scene;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;

/**
 * @author Maximilian Li
 *
 */
public class RootLayoutController {
    
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
	protected void handleAbout(ActionEvent event) {
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
	 * @param event ActionEvent
	 */
	@FXML
	protected void handleClose(ActionEvent event) {
		System.exit(0);
	}
	
	/**
	 * Adds the SequentView to the CENTER Position
	 * @param event ActionEvent
	 * @throws IOException 
	 */
	@FXML
	protected void handleSequentView(ActionEvent event) {
	    //System.out.println(event.getSource());
	    
	    try {
	        FXMLLoader loader = new FXMLLoader();
	        loader.setLocation(MainApp.class.getResource("view/SequentView.fxml"));
	        AnchorPane sequentView = (AnchorPane) loader.load();
	        
	        mainPane.setCenter(sequentView);
	    } catch (IOException e) {
	        e.printStackTrace();
	    }
	    
		//mainPane.setCenter(node);
		//mainView.getChildren().add(new Label("MAINVIEW"));
		
	}
	
	/**
     * Adds the SequentView to the CENTER Position
     * @param event ActionEvent
     * @throws IOException 
     */
    @FXML
    protected void handleMainView(ActionEvent event) {
        //System.out.println(event.getSource());
        
        try {
            FXMLLoader loader = new FXMLLoader();
            loader.setLocation(MainApp.class.getResource("view/MainView.fxml"));
            AnchorPane mainView = (AnchorPane) loader.load();
            
            mainPane.setCenter(mainView);
        } catch (IOException e) {
            e.printStackTrace();
        }
        
        //mainPane.setCenter(node);
        //mainView.getChildren().add(new Label("MAINVIEW"));
        
    }
	
	/**
	 * 
	 */
	public RootLayoutController() {
		// TODO Auto-generated constructor stub
	}

}
