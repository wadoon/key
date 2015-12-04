package de.uka.ilkd.key.nui.view.menu;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewInformation;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.view.RootLayoutController;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.Node;
import javafx.scene.control.Tab;

public class ViewContextMenuController extends ViewController{
    
    private ViewInformation viewInformation;
    public void setParentView(ViewInformation view){
        viewInformation = view;
    }
    
    @Override
    public void initialize(URL location, ResourceBundle resources) {
    }
    
    @FXML
    private void handleTopLeft(ActionEvent event){
        viewInformation.setCurrentPosition(ViewPosition.TOPLEFT);
    }
    
    @FXML
    private void handleTopRight(ActionEvent event){
        viewInformation.setCurrentPosition(ViewPosition.TOPRIGHT);
    }
    
    @FXML
    private void handleBottomLeft(ActionEvent event){
        viewInformation.setCurrentPosition(ViewPosition.BOTTOMLEFT);
    }
    
    @FXML
    private void handleBottomRight(ActionEvent event){
        viewInformation.setCurrentPosition(ViewPosition.BOTTOMRIGHT);
    }
    
    @FXML
    private void handleCenter(ActionEvent event){
        viewInformation.setCurrentPosition(ViewPosition.CENTER);
    }
    
}
