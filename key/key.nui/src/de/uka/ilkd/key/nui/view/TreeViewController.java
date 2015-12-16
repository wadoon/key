package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import javafx.fxml.FXML;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

@KeYView(title="Tree",path="TreeView.fxml",preferredPosition=ViewPosition.TOPLEFT)
public class TreeViewController extends ViewController{
    // Reference to the main application.
    @FXML private TreeView<String> treeView;
    
    public void setRoot(TreeItem<String> t) {
    	treeView.setRoot(t);
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        TreeItem<String> root = new TreeItem<String>("RootNode");
        for (int i=0; i<20; i++) {
            root.getChildren().add(new TreeItem<String>("" + i));
        }
        setRoot(root);
    }

    @Override
    public void initializeAfterLoadingFxml() {
        // TODO Auto-generated method stub
        
    }
}
