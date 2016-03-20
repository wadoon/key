package de.uka.ilkd.key.nui;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.util.KeyFxmlLoader;
import javafx.fxml.Initializable;
import javafx.scene.control.Control;
import javafx.scene.control.Tooltip;
import javafx.stage.Stage;
import javafx.util.Pair;

/**
 * This is the super class for every View Controller.
 * 
 * @author Nils Muzzulini
 *
 */
public abstract class ViewController implements Initializable {

    private MainApp mainApp;
    private Context context;
    private Stage stage;

    public MainApp getMainApp() {
        return mainApp;
    }

    public void setMainApp(MainApp mainApp, Context context) {
        this.mainApp = mainApp;
        this.context = context;
        initializeAfterLoadingFxml();
        setTooltips();
    }

    public Context getContext() {
        return context;
    }

    public Stage getStage() {
        return stage;
    }

    public void setStage(Stage stage) {
        this.stage = stage;
    }

    public <T> Pair<T, ViewController> loadFxmlViewController(URL path) {
        Pair<T, ViewController> pair = KeyFxmlLoader.loadFxml(path);
        pair.getValue().setMainApp(mainApp, context);
        return pair;
    }

    @SuppressWarnings("unchecked")
    public <T> T loadFxmlFromContext(URL path) {
        return (T) loadFxmlViewController(path).getKey();
    }

    /**
     * Virtual method to be implemented if needed. This function is called after
     * the FXML is loaded.
     */
    public void initializeAfterLoadingFxml() {
    }

    /**
     * Virtual method, called when an already loaded view is closed by the user.
     */
    public void viewSuspended() {
    }

    /**
     * Virtual method, called when an already loaded view that was suspended is
     * opened again.
     */
    public void viewReactivated() {
    }

    /**
     * Virtual method to be implemented if needed. This function is called first
     * when any {@link ViewController} is loaded.
     */
    public void initialize(URL location, ResourceBundle resources) {
    }

    /**
     * Virtual method. Sets tooltips for chosen elements in the corresponding
     * view.
     * <p>
     * To implement use {@link Control#setTooltip(Tooltip)} to set a
     * {@link Tooltip} for the desired {@link Control}.
     */
    public void setTooltips() {
    }
}