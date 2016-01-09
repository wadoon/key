package de.uka.ilkd.key.nui;

import java.net.URL;

import de.uka.ilkd.key.nui.model.Context;
import de.uka.ilkd.key.nui.util.KeyFxmlLoader;
import javafx.fxml.Initializable;
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

    public <T> T loadFxmlFromContext(URL path) {
        return (T) loadFxmlViewController(path).getKey();
    }

    public MainApp getMainApp() {
        return mainApp;
    }

    public Context getContext() {
        return context;
    }
    /**
     * Virtual method to be implemented if needed. This function is called after
     * the FXML is loaded.
     */
    public void initializeAfterLoadingFxml() {
    }
}