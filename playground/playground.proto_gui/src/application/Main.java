package application;
	
import javafx.application.Application;
import javafx.event.ActionEvent;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.web.HTMLEditor;
import javafx.stage.Stage;




public class Main extends Application {
	
	int proofCount = 0;
	@Override
	public void start(Stage primaryStage) {
		try {
			//Set Basic Window
			primaryStage.setTitle("Editor");
			primaryStage.setWidth(1024);
			primaryStage.setHeight(768);
			
			//Set Grid for Scene
			BorderPane pane = new BorderPane();
			pane.setPadding(new Insets(25));;
			
			HBox topBox = new HBox();
			pane.setTop(topBox);
			
			//Debugoption Grid
			//grid.setGridLinesVisible(true);
			
			//Setup Menubar and the menus
			mainMenuBar menuBar = new mainMenuBar();
			topBox.getChildren().add(menuBar);
			
			//SetUp startProof Button
			Button startProof = new Button("Start Proof");
			topBox.getChildren().add(startProof);
			
			
			
			
			//Setup Treeview
			TreeView<String> treeView = new TreeView<String>();
			pane.setLeft(treeView);
			TreeItem<String> root = new TreeItem<String>();
			
			
			//SetUp HTML Editor
			final HTMLEditor htmlEditor = new HTMLEditor();
			htmlEditor.setPrefHeight(245);
			pane.setCenter(htmlEditor);
			
			startProof.setOnAction((ActionEvent e) -> {
				System.out.println("Start Proof");
				htmlEditor.setHtmlText(htmlEditor.getHtmlText() +  "</br> Start Proof");
				//Setup the Items
				for(int i = 0; i < 100; i++){
					root.setValue("Proof Root " + proofCount);
					root.getChildren().add(new TreeItem<String>("Message " + i));
					for (int j = 0; j < 100; j++)
					root.getChildren().get(i).getChildren().add(new TreeItem<String>("Node " + i + " SubItem " +j));
				}
				proofCount++;
				treeView.setRoot(root);
			});
			
			//Scene scene = new Scene(htmlEditor);
			Scene scene = new Scene(pane);
			
			
			primaryStage.setScene(scene);
			primaryStage.show();
		} catch(Exception e) {
			e.printStackTrace();
		}
	}
	
	public static void main(String[] args) {
		launch(args);
	}
}
