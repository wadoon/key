package de.uka.ilkd.key.nui.view;

import de.uka.ilkd.key.nui.MainApp;
import javafx.fxml.FXML;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

public class TreeViewController {
    // Reference to the main application.
    private MainApp mainApp;
    @FXML private TreeView<String> treeView;
    /**
     * Is called by the main application to give a reference back to itself.
     * 
     * @param mainApp
     */
    public void setMainApp(MainApp mainApp) {
        this.mainApp = mainApp;
    }
    
    public void setRoot(TreeItem<String> t) {
    	treeView.setRoot(t);
    }
}
