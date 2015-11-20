package de.uka.ilkd.key.nui;

import java.io.IOException;
import java.util.Arrays;
import java.util.Set;

import org.reflections.Reflections;

import de.uka.ilkd.key.nui.view.RootLayoutController;
import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Scene;
import javafx.scene.image.Image;
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;

public class MainApp extends Application {

	private Stage primaryStage;
	private BorderPane rootLayout;
	private RootLayoutController rootLayoutController;

	/**
	 * Constant Strings for positioning
	 */
	private final int centerPos = 0;
	private final int topLeftPos = 1;
	private final int bottomLeftPos = 2;
	private final int topRightPos = 3;
	private final int bottomRightPos = 4;

	@Override
	public void start(Stage primaryStage) {
		this.primaryStage = primaryStage;
		this.primaryStage.setTitle("KeY Project");

		// Set the application icon.
		this.primaryStage.getIcons().add(new Image("file:resources/images/key-color-icon-square.png"));

		initRootLayout();
		registerViews();
		scanForViews();
		scanForMenus();
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

	private void registerViews() {
		// rootLayoutController.registerView("Sequent",
		// MainApp.class.getResource("view/SequentView.fxml"), centerPos);
		rootLayoutController.registerView("Main", MainApp.class.getResource("view/MainView.fxml"), bottomLeftPos);
		rootLayoutController.registerView("Tree", MainApp.class.getResource("view/TreeView.fxml"), topLeftPos);
		// rootLayoutController.registerMenu(MainApp.class.getResource("testimplementation/TestMenuEntry.fxml"));
	}

	private Reflections reflections = new Reflections("de.uka.ilkd.key.nui");

	private void scanForViews() {
		Set<Class<?>> annotated = reflections.getTypesAnnotatedWith(KeYView.class);
		for (Class<?> c : annotated) {
			KeYView annot = c.getAnnotation(KeYView.class);
			if (Arrays.asList(annot.windows()).contains("Main"))
				rootLayoutController.registerView(annot.title(), c.getResource(annot.path()),
						annot.preferredPosition());
		}
		System.out.println("Views: " + annotated.size());
	}

	private void scanForMenus() {
		Set<Class<?>> annotated = reflections.getTypesAnnotatedWith(KeYMenu.class);
		for (Class<?> c : annotated) {
			KeYMenu annot = c.getAnnotation(KeYMenu.class);
			if (Arrays.asList(annot.windows()).contains("Main"))
				rootLayoutController.registerMenu(c.getResource(annot.path()));
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