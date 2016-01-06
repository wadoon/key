package de.uka.ilkd.key.nui;

import javafx.fxml.Initializable;

/**
 * This is the super class for every View Controller.
 * @author Nils Muzzulini
 *
 */
public abstract class ViewController implements Initializable {

    protected Context context;
    protected MainApp mainApp;

    public void setMainApp(MainApp mainApp, Context context) {
        this.mainApp = mainApp;
        this.context = context;
        initializeAfterLoadingFxml();
    }
    
    /**
     * Virtual method to be implemented if needed. This function is called after the FXML is loaded.
     */
    public void initializeAfterLoadingFxml() {
        
    }
}