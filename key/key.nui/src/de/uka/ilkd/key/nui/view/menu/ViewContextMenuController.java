package de.uka.ilkd.key.nui.view.menu;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.view.RootLayoutController;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.Node;
import javafx.scene.control.Tab;

public class ViewContextMenuController extends ViewController{
    private RootLayoutController controller;
    private Tab tab;
    public void setParentView(RootLayoutController controller, Tab tab){
        this.controller = controller;
        this.tab = tab;
    }
    
    @Override
    public void initialize(URL location, ResourceBundle resources) {
    }
    
    @FXML
    private void handleTopLeft(ActionEvent event){
        controller.moveView(tab, ViewPosition.TOPLEFT);
    }
    
    @FXML
    private void handleTopRight(ActionEvent event){
        controller.moveView(tab, ViewPosition.TOPRIGHT);
    }
    
    @FXML
    private void handleBottomLeft(ActionEvent event){
        controller.moveView(tab, ViewPosition.BOTTOMLEFT);
    }
    
    @FXML
    private void handleBottomRight(ActionEvent event){
        controller.moveView(tab, ViewPosition.BOTTOMRIGHT);
    }
    
    @FXML
    private void handleCenter(ActionEvent event){
        controller.moveView(tab, ViewPosition.CENTER);
    }
    
}
