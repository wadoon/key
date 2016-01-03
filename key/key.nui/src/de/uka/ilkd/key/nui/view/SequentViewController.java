package de.uka.ilkd.key.nui.view;

import java.io.File;
import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.IProofListener;
import de.uka.ilkd.key.nui.model.ProofEvent;
import de.uka.ilkd.key.nui.util.SequentPrinter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Proof;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.scene.control.ToggleButton;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.Pane;
import javafx.application.Platform;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.scene.control.CheckBox;
import javafx.scene.control.TextField;
import javafx.scene.input.KeyEvent;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;

@KeYView(title = "Sequent", path = "SequentView.fxml", preferredPosition = ViewPosition.CENTER)

public class SequentViewController extends ViewController {

    private boolean sequentLoaded = false;
    private SequentPrinter printer;
    private LogicPrinter logicPrinter;
    private String proofString;
    private WebEngine webEngine;
    private NotationInfo notationInfo = new NotationInfo();
    private Services services;
    private Sequent sequent;
    private IProofListener proofChangeListener = new IProofListener() {

        @Override
        public void proofUpdated(ProofEvent proofEvent) {
            // execute ui update on javafx thread
            Platform.runLater(new Runnable() {
                @Override
                public void run() {
                    showRootSequent();
                }
            });

        }
    };

    // @FXML
    // private TextArea textArea;

    @FXML
    private ToggleButton searchButton;

    @FXML
    private Pane searchParent;

    @FXML
    private CheckBox checkBoxPrettySyntax;

    @FXML
    private CheckBox checkBoxUnicode;

    @FXML
    private CheckBox checkBoxRegexSearch;

    @FXML
    private WebView textAreaWebView;

    @FXML
    private TextField searchBox;

    private EventHandler<MouseEvent> mousehandler = new EventHandler<MouseEvent>() {

        @Override
        public void handle(MouseEvent mouseEvent) {

            System.out.println(
                    mouseEvent.getEventType() + "\n" + "X : Y - " + mouseEvent.getX() + " : " + mouseEvent.getY() + "\n"
                            + "SceneX : SceneY - " + mouseEvent.getSceneX() + " : " + mouseEvent.getSceneY() + "\n"
                            + "ScreenX : ScreenY - " + mouseEvent.getScreenX() + " : " + mouseEvent.getScreenY());

        }
    };

    /**
     * The constructor. The constructor is called before the initialize()
     * method.
     */
    public SequentViewController() {
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        toggleSearch();
        initializeSearchBox();
        checkBoxPrettySyntax.setDisable(true);
        checkBoxUnicode.setDisable(true);
        searchButton.setDisable(true);
    }

    @Override
    public void initializeAfterLoadingFxml() {
        context.getProofManager().addProofListener(proofChangeListener);
    }

    private void initializeSearchBox() {
        searchBox.setText("Search...");
        searchBox.focusedProperty().addListener(new ChangeListener<Boolean>() {
            @Override
            public void changed(ObservableValue<? extends Boolean> arg0, Boolean oldPropertyValue,
                    Boolean newPropertyValue) {
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
                printer.setFreeTextSearch(searchBox.getText());
                // highlight(searchBox.getText());
                // updateHtml(printer.printSequent(printer.highlightString(proofString,
                // searchBox.getText())));
                updateHtml(printer.printSequent(proofString));
                event.consume();
            }
        });
    }

    @FXML
    private void toggleSearch() {
        searchParent.managedProperty().bind(searchParent.visibleProperty());
        searchParent.setVisible(searchButton.isSelected());
    }

    /**
     * After a proof has been loaded, the sequent of the root node will be
     * displayed
     */
    private void showRootSequent() {
        Proof proof = context.getProofManager().getProof();
        services = proof.getServices();
        sequent = proof.root().sequent();

        logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo, services);
        printSequent();

        checkBoxPrettySyntax.setDisable(false);
        checkBoxUnicode.setDisable(false);
        searchButton.setDisable(false);

        // textAreaWebView.setOnMouseMoved(mousehandler);
    }

    /**
     * Enables/Disables Pretty Syntax.
     */
    @FXML
    private void usePrettySyntax() {
        logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo, services);
        if (!checkBoxPrettySyntax.isSelected()) {
            notationInfo.refresh(services, false, false);
            checkBoxUnicode.setSelected(false);
            checkBoxUnicode.setDisable(true);
            printSequent();
            return;
        }
        else {
            notationInfo.refresh(services, true, false);
            checkBoxUnicode.setDisable(false);
            printSequent();
        }
    }

    /**
     * Enables/Disables Unicode.
     */
    @FXML
    private void useUnicode() {
        logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo, services);
        if (!checkBoxUnicode.isSelected()) {
            notationInfo.refresh(services, true, false);
            printSequent();
            return;
        }
        else {
            notationInfo.refresh(services, true, true);
            printSequent();
        }
    }

    /**
     * Enables/Disables Regex Search
     */
    @FXML
    private void useRegex() {
        printer.setUseRegex(checkBoxRegexSearch.isSelected());
    }
    /**
     * Helper method to print a sequent into the webview.
     */
    private void printSequent() {
        logicPrinter.printSequent(sequent);
        proofString = logicPrinter.toString();

        printer = new SequentPrinter("resources/css/sequentStyle.css", "resources/css/sequentClasses.ini");
        sequentLoaded = true;
        // System.out.println(printer.escape(proofString));
        updateHtml(printer.printSequent(proofString));
    }

    /**
     * Loads a default proof and displays the sequent of its root node.
     */
    @FXML
    private void loadDefaultProof() {
        context.getProofManager().loadProblem(new File("resources/proofs/gcd.closed.proof"));
        // File file = new File("resources/proofs/gcd.closed.proof");
        // mainApp.setProof(file);
        // showRootSequent();
    }

    // TODO replace
    private void highlight(String s) {
        if (!s.isEmpty()) {
            String text = proofString;
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

    private void updateHtml(String s) {
        webEngine = textAreaWebView.getEngine();
        webEngine.loadContent(s);

        // textAreaWebView.getEngine().loadContent(s);
    }
}
