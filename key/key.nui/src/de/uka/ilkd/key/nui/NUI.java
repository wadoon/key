package de.uka.ilkd.key.nui;

import java.io.File;
import java.lang.annotation.Annotation;
import java.util.HashMap;
import java.util.PropertyResourceBundle;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.controller.ControllerAnnotation;
import de.uka.ilkd.key.nui.controller.MainViewController;
import de.uka.ilkd.key.nui.controller.MainViewController.Place;
import de.uka.ilkd.key.nui.controller.NUIController;
import de.uka.ilkd.key.nui.controller.TreeViewController;
import de.uka.ilkd.key.nui.exceptions.ComponentNotFoundException;
import de.uka.ilkd.key.nui.exceptions.ControllerNotFoundException;
import de.uka.ilkd.key.nui.exceptions.ToggleGroupNotFoundException;
import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Scene;
import javafx.scene.control.Menu;
import javafx.scene.control.RadioMenuItem;
import javafx.scene.control.ToggleGroup;
import javafx.scene.image.Image;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Pane;
import javafx.stage.Stage;

/**
 * Main Class for initializing the GUI.
 * 
 * @author Florian Breitfelder
 * @author Patrick Jattke
 *
 */
public class NUI extends Application {

    /**
     * The proof file initially (at program startup) loaded.
     */
    private static File initialProofFile;

    /**
     * The main method.
     * 
     * @param args
     *            The arguments passed to the program. Can take the path to a
     *            proof file as argument, which is loaded right after program
     *            startup.
     */
    public static void main(final String... args) {
        if (args.length != 0) {
            initialProofFile = new File(
                    System.getProperty("user.dir") + args[0]);
        }
        launch(args);
    }

    /**
     * Contains references to all loaded controllers, where <br \>
     * <ul>
     * <li>String is the fx:id of the loaded controller.
     * <li>NUIController is the reference to the loaded controller.
     * </ul>
     */
    private HashMap<String, NUIController> controllers = new HashMap<>();

    /**
     * Contains the loaded components, where
     * <ul>
     * <li>String represents the fx:id of the loaded component.
     * <li>Pane is the reference to the loaded component.
     * </ul>
     */
    private HashMap<String, Pane> components = new HashMap<>();

    /**
     * Contains the loaded toggle groups, where
     * <ul>
     * <li>String represents the fx:id of the loaded toggle group.
     * <li>ToggleGroup is the reference to the loaded toggle group.
     * </ul>
     */
    private HashMap<String, ToggleGroup> toggleGroups = new HashMap<>();

    /**
     * The currently loaded resource bundle (language file).
     */
    private ResourceBundle bundle = null;

    /**
     * The root border pane where all others components get loaded in.
     */
    private BorderPane root = null;

    /**
     * The FXML Loader used to load the other controllers and components.
     */
    private FXMLLoader fxmlLoader = null;

    /**
     * A reference to the {@link MainViewController}.
     */
    private MainViewController mainViewController = null;

    /**
     * The menu "View" of the menu bar.
     */
    private Menu viewPositionMenu = null;

    /**
     * The data model used to store the loaded proof as a {@link TreeViewState}.
     */
    private DataModel dataModel;

    /**
     * When program is starting method "start" is called. Loads the stage and
     * scene.
     */
    @Override
    public final void start(final Stage stage) throws Exception {
        initializeNUI();

        // Load scene and set preferences
        final Scene scene = new Scene(root, 1024, 768);
        stage.setTitle("KeY");
        stage.getIcons().add(new Image(
                getClass().getResourceAsStream("images/KeY-Mono.png")));
        stage.setScene(scene);
        stage.show();

        // Assign event when stage closing event is elevated
        stage.setOnCloseRequest((e) -> {
            try {
                ((MainViewController) getController("MainView"))
                        .handleCloseWindow(e);
            }
            catch (ControllerNotFoundException e1) {
                e1.showMessage();
            }
        });
    }

    /**
     * Initializes the application, such as all components, all controllers and
     * views.
     * 
     * @throws Exception
     */
    public void initializeNUI() throws Exception {
        // Load Main View
        String filename = "MainView.fxml";
        String name = filename.substring(0, filename.lastIndexOf("."));

        bundle = new PropertyResourceBundle(
                getClass().getResourceAsStream("bundle_en_EN.properties"));
        dataModel = new DataModel(this, bundle);
        fxmlLoader = new FXMLLoader(getClass().getResource(filename), bundle);
        System.out.println("start launched successfully.");
        root = fxmlLoader.load();
        components.put("MainView", root);

        mainViewController = fxmlLoader.getController();
        mainViewController.constructor(this, dataModel, bundle, name, filename);
        controllers.put("MainView", mainViewController);

        // initialize viewPositionMenu
        viewPositionMenu = new Menu(bundle.getString("configViews"));
        viewPositionMenu.setId("configViews");

        // Load all components
        loadComponents();

        ((TreeViewController) getController("treeViewPane")).addSearchView(
                getComponent("searchViewPane"),
                getController("searchViewPane"));
        // create file menu for MainView
        mainViewController.getViewMenu().getItems().add(viewPositionMenu);

        // place component on MainView
        mainViewController.addComponent(getComponent("treeViewPane"),
                Place.LEFT);
        mainViewController.addComponent(getComponent("proofViewPane"),
                Place.MIDDLE);
        mainViewController.addComponent(getComponent("strategyViewPane"),
                Place.RIGHT);
        mainViewController.addComponent(getComponent("openProofsViewPane"),
                Place.BOTTOM);
    }

    /**
     * Loads the FXML components and stores the references to
     * <ul>
     * <li>the controllers in {@link #controllers}
     * <li>the components in {@link #components}
     * <li>the toggle groups in {@link #toggleGroups}.
     * </ul>
     * 
     * @throws Exception
     */
    private void loadComponents() throws Exception {
        File[] files = new File(getClass().getResource("components").getPath())
                .listFiles();
        FXMLLoader fxmlLoader = null;
        for (File file : files) {
            if (file.isFile() && file.getName().matches(".*[.fxml]")) {
                fxmlLoader = new FXMLLoader(
                        getClass().getResource("components/" + file.getName()),
                        bundle);

                Pane component = fxmlLoader.load();
                components.put(component.getId(), component);
                NUIController nuiController;// = new NUIController();
                // before you can get the controller
                // you have to call fxmlLoader.load()
                nuiController = fxmlLoader.getController();
                if (nuiController != null)
                    nuiController.constructor(this, dataModel, bundle,
                            component.getId(), file.getName());
                controllers.put(component.getId(), nuiController);

                // get all annotations of type ControllerAnnotation
                // if no annotations are present, returns a array of length 0
                Annotation[] annotations = nuiController.getClass()
                        .getAnnotationsByType(ControllerAnnotation.class);

                // create a view position menu for every component
                for (Annotation annotation : annotations) {
                    if (((ControllerAnnotation) annotation).createMenu()) {
                        ToggleGroup toggleGroup = new ToggleGroup();
                        toggleGroups.put(component.getId(), toggleGroup);
                        viewPositionMenu.getItems().add(
                                createSubMenu(component.getId(), toggleGroup));
                        break;
                    }
                }
            }
        }
    }

    /**
     * Creates sub menu entries for the "View" menu.
     * 
     * @param menuName
     *            The name of the menu where sub menu should be added to.
     * @param toggleGroup
     *            The toggle group containing the sub menu entries.
     * @return The constructed Menu.
     */
    private Menu createSubMenu(String menuName, ToggleGroup toggleGroup) {
        Menu menu = new Menu(bundle.getString(menuName));
        String hideText = bundle.getString("hide");
        String leftText = bundle.getString("left");
        String rightText = bundle.getString("right");
        String bottomText = bundle.getString("bottom");
        String middleText = bundle.getString("middle");

        addRadioMenuItem(hideText, menuName, toggleGroup, true, Place.HIDDEN,
                menu);

        addRadioMenuItem(leftText, menuName, toggleGroup, false, Place.LEFT,
                menu);

        addRadioMenuItem(rightText, menuName, toggleGroup, false, Place.RIGHT,
                menu);

        addRadioMenuItem(bottomText, menuName, toggleGroup, false, Place.BOTTOM,
                menu);

        addRadioMenuItem(middleText, menuName, toggleGroup, false, Place.MIDDLE,
                menu);

        return menu;
    }

    /**
     * Creates a radio menu item entry and adds it to the given Menu
     * <code>destinationMenu</code>.
     * 
     * @param menuItemName
     *            The fx:id and shown name of the menu entry.
     * @param componentName
     *            The component name associated with.
     * @param tGroup
     *            The toggle group where the item belongs to.
     * @param isSelected
     *            Specifies whether the item is selected by default or not.
     * @param position
     *            The position of the view associated with the menu item entry.
     * @param destinationMenu
     *            The destination menu where the menu item should be added to.
     */
    private void addRadioMenuItem(String menuItemName, String componentName,
            ToggleGroup tGroup, Boolean isSelected, Place position,
            Menu destinationMenu) {
        RadioMenuItem menuItem = new RadioMenuItem(menuItemName);
        menuItem.setOnAction(mainViewController.getNewHandleLoadComponent());
        menuItem.setId(menuItemName);
        menuItem.getProperties().put("componentName", componentName);
        menuItem.setToggleGroup(tGroup);
        menuItem.setSelected(isSelected);
        menuItem.setUserData(position);
        destinationMenu.getItems().add(menuItem);
    }

    /**
     * Returns the component with the specified fx:id of the list of loaded
     * components {@link #components}.
     * 
     * @param name
     *            The fx:id of the component.
     * @return A reference to a pane corresponding to the given fx:id.
     * @throws ComponentNotFoundException
     *             If no component with the given fx:id was found.
     */
    public Pane getComponent(String name) throws ComponentNotFoundException {
        if (!components.containsKey(name))
            throw new ComponentNotFoundException(name);
        return components.get(name);
    }

    /**
     * Returns the controller with the specified fx:id of the list of loaded
     * controller {@link #controllers}.
     * 
     * @param name
     *            The fx:id of the controller.
     * @return A subclass of NUIController, which is a reference to the
     *         controller.
     * @throws ControllerNotFoundException
     *             If no controller with the given fx:id was found.
     */
    public NUIController getController(String name)
            throws ControllerNotFoundException {
        if (!controllers.containsKey(name))
            throw new ControllerNotFoundException(name);
        return controllers.get(name);
    }

    public ToggleGroup getToggleGroup(String name)
            throws ToggleGroupNotFoundException {
        if (!toggleGroups.containsKey(name))
            throw new ToggleGroupNotFoundException(name);
        return toggleGroups.get(name);
    }

    /**
     * Returns the main border pane containing all other components.
     * 
     * @return BorderPane where all other components are in.
     */
    public BorderPane getRoot() {
        return root;
    }

    /**
     * Returns the proof file initially loaded.
     * 
     * @return initialProofFile the proof file initially loaded
     */
    public static File getInitialProofFile() {
        return initialProofFile;
    }

    /**
     * Updates the status bar on the mainView by the given text. Keeps the text
     * on the status bar till the next update is performed.
     * 
     * @param text
     *            String to be set to the status bar.
     */
    public void updateStatusbar(String text) {
        try {
            ((MainViewController) getController("MainView"))
                    .updateStatusbar(text);
        }
        catch (ControllerNotFoundException e) {
            e.showMessage();
            e.printStackTrace();
        }
    }

    /**
     * Returns a reference to the DataModel.
     * 
     * @return dataModel
     */
    public DataModel getDataModel() {
        return dataModel;
    }

    /**
     * returns a text from the language file which corresponds to the textId
     * 
     * @param textId
     * @return
     */
    public String getText(String textId) {
        return bundle.getString(textId);
    }
}
