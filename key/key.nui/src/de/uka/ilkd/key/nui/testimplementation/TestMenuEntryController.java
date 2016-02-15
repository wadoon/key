package de.uka.ilkd.key.nui.testimplementation;

import java.net.URL;
import java.util.ResourceBundle;
import java.util.Set;

import de.uka.ilkd.key.nui.KeYMenu;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewObserver;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.ViewInformation;
import de.uka.ilkd.key.nui.util.KeyFxmlLoader;
import de.uka.ilkd.key.nui.util.SerializableViewInformation;
import de.uka.ilkd.key.nui.view.SequentViewController;
import de.uka.ilkd.key.proof.Node;
import javafx.application.Platform;
import javafx.event.ActionEvent;
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
    
    @FXML
    private void openNewSequentView(ActionEvent event) {
        Node node = getContext().getKeYMediator().getSelectedNode();
        
        ViewInformation info = new ViewInformation(node.name(), SequentViewController.class.getResource("SequentView.fxml"),
                ViewPosition.CENTER, false);
        
        info.addObserver(new ViewObserver(getMainApp().getRootLayoutController()));
        info.setIsActive(true);
        
        Platform.runLater(() -> {
            ((SequentViewController)info.getController()).loadProofToView(node);
        });
    }
}
