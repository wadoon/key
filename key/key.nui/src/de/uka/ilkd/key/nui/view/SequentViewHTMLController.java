package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.util.SequentPrinter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import javafx.fxml.FXML;
import javafx.scene.control.ToggleButton;
import javafx.scene.layout.Pane;
import javafx.scene.web.HTMLEditor;

@KeYView(title="SequentHTML",path="SequentViewHTML.fxml",preferredPosition=ViewPosition.CENTER)
public class SequentViewHTMLController extends SequentViewController {

    @FXML
    private HTMLEditor textAreaHTML;

    @FXML
    private ToggleButton filterButton;

    @FXML
    private Pane filterParent;

    /**
     * The constructor.
     * The constructor is called before the initialize() method.
     */
    public SequentViewHTMLController() {
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
        
        String proofString;
        proofString = logicPrinter.toString();
        SequentPrinter printer = new SequentPrinter("resources/css/sequentStyle.css");
        //System.out.println(printer.escape(proofString));
        
        textAreaHTML.setHtmlText(printer.printSequent(proofString));
    }
    
    @Override
    public void initialize(URL location, ResourceBundle resources) {
        // hide the filter at the beginning
        textAreaHTML.lookup(".top-toolbar").setManaged(false);
        textAreaHTML.lookup(".top-toolbar").setVisible(false);

        textAreaHTML.lookup(".bottom-toolbar").setManaged(false);
        textAreaHTML.lookup(".bottom-toolbar").setVisible(false);
        toggleFilter();
    }

    @FXML
    private void toggleFilter(){
        filterParent.managedProperty().bind(filterParent.visibleProperty());
        filterParent.setVisible(filterButton.isSelected());
    }
}
