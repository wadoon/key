package de.uka.ilkd.key.nui.view;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
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

@KeYView(title="Sequent",path="SequentView.fxml",preferredPosition=0)
public class SequentViewController extends ViewController {

    @FXML
    private TextArea textArea;
    
    @FXML
    private TextField textField;
    
    private Proof proof;
    
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
     * Opens a file chooser to select a proof and loads that proof.
     */
    @FXML
    private void chooseProof() {
        textField.setText("Loading Proof...");
        FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle("Select a proof to load");
        fileChooser.getExtensionFilters().addAll(new ExtensionFilter("Proofs", "*.proof"),
                new ExtensionFilter("All Files", "*.*"));
        fileChooser.setInitialDirectory(new File("../"));
        
        File file = fileChooser.showOpenDialog(new Stage());
        
        if (file == null) {
            textField.setText("No File Selected");
            return;
        }
        
        proof = loadProof(file);
        textField.appendText("\n Proof loaded: " + file.getName());
    }
    
    /**
     * After a proof has been loaded, the sequent of the root node can be displayed
     */
    @FXML
    private void showRootSequent() {
        if (proof == null) {
            textField.setText("Please Select a Proof first.");
            return;
        }
        Node node = proof.root();
        Sequent sequent = node.sequent();
        LogicPrinter logicPrinter = new LogicPrinter(new ProgramPrinter(), new NotationInfo(), proof.getServices());
        
        logicPrinter.printSequent(sequent);
        
        textArea.setText(logicPrinter.toString());
    }
    
    /**
     * Loads the given proof file. Checks if the proof file exists and the proof
     * is not null, and fails if the proof could not be loaded.
     *
     * @param proofFileName
     *            The file name of the proof file to load.
     * @return The loaded proof.
     */
    private Proof loadProof(File proofFile) {
        //File proofFile = new File("../" + proofFileName);

        try {
            KeYEnvironment<?> environment = KeYEnvironment.load(
                    JavaProfile.getDefaultInstance(), proofFile, null, null,
                    null, true);
            Proof proof = environment.getLoadedProof();

            return proof;
        }
        catch (ProblemLoaderException e) {
            e.printStackTrace();
            return null;
        }
    }
}
