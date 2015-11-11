/**
 * 
 */
package de.uka.ikd.key.nui;

import java.io.IOException;

import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;

/**
 * @author Maximilian Li
 *
 */
public class MenuController {
	
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
	 */
	@FXML
	protected void handleSequentView(ActionEvent event){
		mainPane.setCenter(new Label("SEQUENT VIEW"));
		//mainView.getChildren().add(new Label("MAINVIEW"));
		
	}
	
	/**
	 * 
	 */
	public MenuController() {
		// TODO Auto-generated constructor stub
	}

}
