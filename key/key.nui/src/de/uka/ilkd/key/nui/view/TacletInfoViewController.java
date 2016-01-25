package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.IProofListener;
import de.uka.ilkd.key.nui.util.TacletInfoPrinter;
import de.uka.ilkd.key.proof.Node;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.scene.control.TextArea;

@KeYView(title = "TacletInfo", path = "TacletInfoView.fxml", preferredPosition = ViewPosition.TOPRIGHT, hasMenuItem = false)
public class TacletInfoViewController extends ViewController {


    private KeYMediator mediator;
    private Node node;
    private TacletInfoPrinter printer;
    @FXML
    private TextArea outputText;
    
    private IProofListener proofChangeListener = (proofEvent) -> {
        // execute ui update on javafx thread
        Platform.runLater(() -> {
            showTacletInfo();
        });
    };
    
    @Override
    public void initialize(URL arg0, ResourceBundle arg1) {
        outputText.setEditable(false);
        outputText.setDisable(true);
        printer = new TacletInfoPrinter();
    }
    
    @Override
    public void initializeAfterLoadingFxml() {
        mediator = getContext().getProofManager().getMediator();
        getContext().getProofManager().addProofListener(proofChangeListener);
    }
    
    /**
     * Display information about applied rules for the given node.
     * @param node
     */
    public void showTacletInfo(Node node){
        outputText.setDisable(false);
        outputText.setText(printer.printTacletInfo(mediator, node));
    };
    
    /**
     * Display information about applied rules for the selected node in the TreeView.
     */
    public void showTacletInfo(){
        showTacletInfo(mediator.getSelectedNode());
    };
}
