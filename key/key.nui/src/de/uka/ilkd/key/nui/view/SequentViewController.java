package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.scene.control.TextArea;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.input.KeyEvent;
import javafx.scene.layout.Pane;

@KeYView(title="Sequent",path="SequentView.fxml",preferredPosition=ViewPosition.CENTER)
public class SequentViewController extends ViewController {

    @FXML
    private TextArea textArea;

    @FXML
    private ToggleButton filterButton;

    @FXML
    private Pane filterParent;
    
    @FXML
    private TextField searchBox;

    /**
     * The constructor.
     * The constructor is called before the initialize() method.
     */
    public SequentViewController() {
        searchBox.setOnKeyTyped(new EventHandler<KeyEvent>() {
            public void handle(KeyEvent event){
                
            }
        });
    }

    /**
     * After a proof has been loaded, the sequent of the root node can be displayed
     */
    @FXML
    private void showRootSequent() {
        Proof proof = mainApp.getProof();
        if (proof == null) {
            mainApp.setStatus("Please Select a Proof first.");
            return;
        }
        Node node = proof.root();
        Sequent sequent = node.sequent();
        LogicPrinter logicPrinter = new LogicPrinter(new ProgramPrinter(), new NotationInfo(), proof.getServices());

        logicPrinter.printSequent(sequent);

        textArea.setText(logicPrinter.toString());
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        // hide the filter at the beginning
        toggleFilter();
    }

    @FXML
    private void toggleFilter(){
        filterParent.managedProperty().bind(filterParent.visibleProperty());
        filterParent.setVisible(filterButton.isSelected());
    }
}
