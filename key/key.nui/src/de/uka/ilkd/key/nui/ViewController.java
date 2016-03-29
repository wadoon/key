package de.uka.ilkd.key.nui;

import java.net.URL;
import java.util.ResourceBundle;
import de.uka.ilkd.key.nui.event.HandlerEvent;
import de.uka.ilkd.key.nui.util.KeyFxmlLoader;
import javafx.fxml.Initializable;
import javafx.scene.control.Control;
import javafx.scene.control.Tooltip;
import javafx.stage.Stage;
import javafx.util.Pair;

/**
 * This is the super class for every View Controller. Call
 * {@link #initViewController(MainApp, Context)} when creating the view to bind
 * the {@link MainApp} and the {@link Context} to it.
 * 
 * @author Nils Muzzulini
 * @author Benedikt Gross
 * @author Victor Schuemmer
 * @author Maximilian Li
 * @version 1.0
 */
public abstract class ViewController implements Initializable {

    private MainApp mainApp;
    private Context context;
    private Stage stage;
    private HandlerEvent<String> titleUpdatedEvent = new HandlerEvent<>();

    /**
     * @return the {@link MainApp}
     */
    public MainApp getMainApp() {
        return mainApp;
    }

    /**
     * An event that is fired each time a new title is set.
     * 
     * @return Title updated event.
     */
    public HandlerEvent<String> getTitleUpdatedEvent() {
        return titleUpdatedEvent;
    }

    /**
     * This method must be called when the view is created. It is used to set
     * the {@link MainApp}, the {@link Context} and initialize {@link Tooltip
     * Tooltips}.
     * 
     * @param mainApp
     * @param context
     */
    public void initViewController(MainApp mainApp, Context context) {
        this.mainApp = mainApp;
        this.context = context;
        initializeAfterLoadingFxml();
        setTooltips();
    }

    /**
     * @return {@link Context}
     */
    public Context getContext() {
        return context;
    }

    /**
     * @return {@link Stage}
     */
    public Stage getStage() {
        return stage;
    }

    /**
     * Set a {@link Stage} for this view.
     * 
     * @param stage
     *            Stage to be set.
     */
    public void setStage(Stage stage) {
        this.stage = stage;
    }

    /**
     * Load an fxml file with the same mainApp and context of this object.
     */
    public <T> Pair<T, ViewController> loadFxmlViewController(URL path) {
        Pair<T, ViewController> pair = KeyFxmlLoader.loadFxml(path);
        pair.getValue().initViewController(mainApp, context);
        return pair;
    }

    /**
     * Load an fxml file with the same mainApp and context of this object.
     */
    @SuppressWarnings("unchecked")
    public <T> T loadFxmlFromContext(URL path) {
        //SuppressWarnings: the type is always T at runtime, just not at compile time.
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

    @Override
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