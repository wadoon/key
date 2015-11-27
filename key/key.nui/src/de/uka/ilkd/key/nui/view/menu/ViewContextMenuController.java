package de.uka.ilkd.key.nui.view.menu;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.view.RootLayoutController;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.Node;

public class ViewContextMenuController extends ViewController{
    private RootLayoutController controller;
    private Node parent;
    public void setParentView(RootLayoutController controller,Node parent){
        this.controller = controller;
        this.parent = parent;
    }
    
    @Override
    public void initialize(URL location, ResourceBundle resources) {
    }
    
    @FXML
    private void handleTopLeft(ActionEvent event){
        controller.moveView(controller.getViewPosition(parent), ViewPosition.TOPLEFT);
    }
    
    @FXML
    private void handleTopRight(ActionEvent event){
        controller.moveView(controller.getViewPosition(parent), ViewPosition.TOPRIGHT);
    }
    
    @FXML
    private void handleBottomLeft(ActionEvent event){
        controller.moveView(controller.getViewPosition(parent), ViewPosition.BOTTOMLEFT);
    }
    
    @FXML
    private void handleBottomRight(ActionEvent event){
        controller.moveView(controller.getViewPosition(parent), ViewPosition.BOTTOMRIGHT);
    }
    
    @FXML
    private void handleCenter(ActionEvent event){
        controller.moveView(controller.getViewPosition(parent), ViewPosition.CENTER);
    }
    
}
