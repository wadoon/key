package de.uka.ilkd.key.nui.testimplementation;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.KeYMenu;
import de.uka.ilkd.key.nui.ViewController;
import javafx.fxml.FXML;

@KeYMenu(path="TestMenuEntry.fxml")
public class TestMenuEntryController extends ViewController {
    
    @FXML
    private void doClose(){
        //System.exit(0);
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        // TODO Auto-generated method stub
        
    }
}
