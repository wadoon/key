package de.uka.ilkd.key.nui.view;

import de.uka.ilkd.key.nui.MainApp;
import de.uka.ilkd.key.nui.ViewController;
import javafx.fxml.FXML;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

public class TreeViewController extends ViewController{
    // Reference to the main application.
    private MainApp mainApp;
    @FXML private TreeView<String> treeView;
    
    public void setRoot(TreeItem<String> t) {
    	treeView.setRoot(t);
    }
    
    @FXML
    private void initialize(){
    	setRoot(new TreeItem<String>("RootNode"));
    }
}
