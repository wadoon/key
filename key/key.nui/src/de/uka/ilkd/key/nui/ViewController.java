package de.uka.ilkd.key.nui;

import java.net.URL;

import de.uka.ilkd.key.nui.model.Context;
import de.uka.ilkd.key.nui.util.KeyFxmlLoader;
import javafx.fxml.Initializable;
import javafx.stage.Stage;
import javafx.util.Pair;

/**
 * This is the super class for every View Controller.
 * 
 * @author Nils Muzzulini
 *
 */
public abstract class ViewController implements Initializable {

    private Context context;
    private MainApp mainApp;
    private Stage stage;

    public void setMainApp(MainApp mainApp, Context context) {
        this.mainApp = mainApp;
        this.context = context;
        initializeAfterLoadingFxml();
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

    public MainApp getMainApp() {
        return mainApp;
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
    
    /**
     * Virtual method to be implemented if needed. This function is called after
     * the FXML is loaded.
     */
    public void initializeAfterLoadingFxml() {
    }
    
    /**
     * Virtual method, called when an already loaded view is closed by the user
     */
    public void viewSuspended(){
        
    }
    
    /**
     * Virtual method, called when an already loaded view that was suspenden is opened again.
     */
    public void viewReactivated(){
        
    }
}