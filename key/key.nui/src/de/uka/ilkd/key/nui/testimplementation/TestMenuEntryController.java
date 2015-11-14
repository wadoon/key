package de.uka.ilkd.key.nui.testimplementation;

import de.uka.ilkd.key.nui.ViewController;
import javafx.fxml.FXML;

public class TestMenuEntryController extends ViewController {
    /**
     * Initializes the controller class. This method is automatically called
     * after the fxml file has been loaded.
     */
    @FXML
    private void initialize() {
    }
    
    @FXML
    private void DoClose(){
        System.exit(0);
    }
}
