package de.uka.ilkd.key.nui.view;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import javafx.fxml.FXML;
import javafx.scene.control.TextArea;
import javafx.scene.control.TextField;
import javafx.stage.FileChooser;
import javafx.stage.FileChooser.ExtensionFilter;
import javafx.stage.Stage;

import java.io.File;

@KeYView(title="Sequent",path="SequentView.fxml",preferredPosition=ViewPosition.CENTER)
public class SequentViewController extends ViewController {

    @FXML
    private TextArea textArea;
    
    @FXML
    private TextField textField;
    
    /**
     * The constructor.
     * The constructor is called before the initialize() method.
     */
    public SequentViewController() {
    }

    /**
     * Initializes the controller class. This method is automatically called
     * after the FXML file has been loaded.
     */
    @FXML
    private void initialize() {
        textField.setText("Welcome to the Sequent View.");
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
}
