package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.List;
import java.util.ResourceBundle;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.util.SequentPrinter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.input.KeyEvent;
import javafx.scene.layout.Pane;
import javafx.scene.web.WebView;

@KeYView(title = "Sequent", path = "SequentView.fxml", preferredPosition = ViewPosition.CENTER)

public class SequentViewController extends ViewController {

    @FXML
    private WebView textAreaHTML;

    @FXML
    private ToggleButton filterButton;

    @FXML
    private Pane filterParent;
    
    @FXML
    private TextField filterText;

    @FXML
    private TextField searchBox;

    /**
     * The constructor. The constructor is called before the initialize()
     * method.
     */
    public SequentViewController() {
    }

    private boolean sequentLoaded = false;
    private SequentPrinter printer;
    private String proofString;

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
        Sequent sequent = node.sequent();
        LogicPrinter logicPrinter = new LogicPrinter(new ProgramPrinter(),
                new NotationInfo(), proof.getServices());

        logicPrinter.printSequent(sequent);

        proofString = logicPrinter.toString();
        printer = new SequentPrinter("resources/css/sequentStyle.css","resources/css/sequentClasses.ini");
        sequentLoaded = true;
        //System.out.println(printer.escape(proofString));
        updateHtml();
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        // hide the filter at the beginning
        toggleFilter();

        searchBox.setText("Search...");
        searchBox.focusedProperty().addListener(new ChangeListener<Boolean>() {
            @Override
            public void changed(ObservableValue<? extends Boolean> arg0,
                    Boolean oldPropertyValue, Boolean newPropertyValue) {
                if (newPropertyValue) {
                    if (searchBox.getText().equals("Search..."))
                        searchBox.setText("");
                }
                else {
                    if (searchBox.getText().isEmpty())
                        searchBox.setText("Search...");
                }
            }
        });
        searchBox.setOnKeyReleased(new EventHandler<KeyEvent>() {
            public void handle(KeyEvent event) {
                highlight(searchBox.getText());
                event.consume();
            }
        });

    }

    //TODO replace
    private void highlight(String s) {
        if (!s.isEmpty()) {
            String text = "dummy";
            int lastIndex = 0;
            while (lastIndex != -1) {
                lastIndex = text.indexOf(s, lastIndex);

                if (lastIndex != -1) {
                    // TODO instead of printing the index, it should be
                    // highlighted in the textArea
                    System.out.println(lastIndex);
                    lastIndex += s.length();
                }
            }
        }
    }

    @FXML
    private void toggleFilter() {
        filterParent.managedProperty().bind(filterParent.visibleProperty());
        filterParent.setVisible(filterButton.isSelected());
    }
    
    private void updateHtml(){
        textAreaHTML.getEngine().loadContent(printer.printSequent(proofString));
    }
    
    @FXML
    private void handleKeyTyped(){
      doFilter(filterText.getText());
    }
    
    //just dummy method
    private void doFilter(String filterstring){
        if(!sequentLoaded)return;
        printer.infuseCSS(String.format("not(%s){display:none;}",filterstring));
        updateHtml();
    }
}
