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
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;

/**
 * @author Maximilian Li
 *
 */
public class RootLayoutController {
    
    // Reference to the main application
    private MainApp mainApp;

    /**
     * Is called by the main application to give a reference back to itself.
     * 
     * @param mainApp
     */
    public void setMainApp(MainApp mainApp) {
        this.mainApp = mainApp;
    }
    
	/**
	 * The BorderPane from the Main Window
	 */
	//@FXML
	//BorderPane mainPane;
	
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
	 * Shows the Sequent View.
	 */
	@FXML
	private void handleSequentView() {
	    mainApp.showSequentView();
	    
		//mainPane.setCenter(node);
		//mainView.getChildren().add(new Label("MAINVIEW"));
	}
	
	/**
     * Shows the Main View.
     */
    @FXML
    private void handleMainView() {
        mainApp.showMainView();
    }
	
	/**
	 * 
	 */
	public RootLayoutController() {
		// TODO Auto-generated constructor stub
	}

}
