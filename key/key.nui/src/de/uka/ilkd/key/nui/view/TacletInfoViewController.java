package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.printer.TacletInfoPrinter;
import de.uka.ilkd.key.proof.Node;
import javafx.fxml.FXML;
import javafx.scene.control.TextArea;

/**
 * ViewController for the area of a sequent view that shows information about
 * applied taclets.
 * 
 * @author Victor Schuemmer
 * @version 1.0
 */
public class TacletInfoViewController extends ViewController {

    private KeYMediator mediator = null;
    @FXML
    private TextArea outputText;

    @Override
    public void initialize(URL arg0, ResourceBundle arg1) {
        outputText.setEditable(false);
        outputText.setDisable(true);
    }

    @Override
    public void initializeAfterLoadingFxml() {
        mediator = getContext().getKeYMediator();
    }

    /**
     * Display information about applied rules for the given {@link Node}.
     * 
     * @param node
     */
    public void showTacletInfo(Node node) {
        outputText.setDisable(false);
        outputText.setText(TacletInfoPrinter.printTacletInfo(mediator, node));
    };

    /**
     * Display information about applied rules for the selected {@link Node} in the
     * TreeView.
     */
    public void showTacletInfo() {
        showTacletInfo(mediator.getSelectedNode());
    };
}
