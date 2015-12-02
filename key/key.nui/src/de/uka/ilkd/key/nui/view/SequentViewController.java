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
import javafx.geometry.Point2D;
import javafx.scene.Scene;
import javafx.scene.control.TextArea;
import javafx.scene.control.ToggleButton;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Pane;
import static javafx.scene.AccessibleAttribute.OFFSET_AT_POINT;

@KeYView(title = "Sequent", path = "SequentView.fxml", preferredPosition = ViewPosition.CENTER)
public class SequentViewController extends ViewController {

    @FXML
    private TextArea textArea;

    @FXML
    private ToggleButton filterButton;

    @FXML
    private Pane filterParent;

    private EventHandler<MouseEvent> mousehandler = new EventHandler<MouseEvent>() {

        @Override
        public void handle(MouseEvent mouseEvent) {
            final int idx = (int) textArea.queryAccessibleAttribute(OFFSET_AT_POINT, new Point2D(mouseEvent.getScreenX(), mouseEvent.getScreenY()));
            //System.out.println(idx);
            System.out.println("Character moved over: " + textArea.getText().charAt(idx));
            /*System.out.println(
                    mouseEvent.getEventType() + "\n" + "X : Y - " + mouseEvent.getX() + " : " + mouseEvent.getY() + "\n"
                            + "SceneX : SceneY - " + mouseEvent.getSceneX() + " : " + mouseEvent.getSceneY() + "\n"
                            + "ScreenX : ScreenY - " + mouseEvent.getScreenX() + " : " + mouseEvent.getScreenY());*/
            
        }
    };
    
    @FXML
    private void MouseHandler() {
        //System.out.println("mouse moved");
    }

    /**
     * The constructor. The constructor is called before the initialize()
     * method.
     */
    public SequentViewController() {
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        // hide the filter at the beginning
        toggleFilter();
    }

    /**
     * After a proof has been loaded, the sequent of the root node can be
     * displayed
     */
    @FXML
    private void showRootSequent() {
        Proof proof = mainApp.getProof();
        if (proof == null) {
            mainApp.setStatus("Please Select a Proof first.");
            return;
        }
        Node node = proof.root();
        System.out.println("number of nodes: " + proof.countNodes());
        System.out.println("getNodeInfo(): " + node.getNodeInfo());
        Sequent sequent = node.sequent();
        //System.out.println(sequent.getFormulabyNr(0).toString());
        LogicPrinter logicPrinter = new LogicPrinter(new ProgramPrinter(), new NotationInfo(), proof.getServices());
        
        logicPrinter.printSequent(sequent);

        textArea.setText(logicPrinter.toString());
        
        textArea.setOnMouseMoved(mousehandler);
    }

    @FXML
    private void toggleFilter() {
        filterParent.managedProperty().bind(filterParent.visibleProperty());
        filterParent.setVisible(filterButton.isSelected());
    }
}
