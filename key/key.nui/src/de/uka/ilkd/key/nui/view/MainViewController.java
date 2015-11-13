package de.uka.ilkd.key.nui.view;

import de.uka.ilkd.key.nui.MainApp;

public class MainViewController {
    
    // Reference to the main application.
    private MainApp mainApp;
    
    /**
     * Is called by the main application to give a reference back to itself.
     * 
     * @param mainApp
     */
    public void setMainApp(MainApp mainApp) {
        this.mainApp = mainApp;
    }
}
