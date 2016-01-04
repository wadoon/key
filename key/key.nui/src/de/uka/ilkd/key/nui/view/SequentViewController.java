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
import de.uka.ilkd.key.nui.util.SequentPrinter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Proof;
import javafx.fxml.FXML;
import javafx.scene.control.ToggleButton;
import javafx.scene.layout.Pane;
import javafx.application.Platform;
import javafx.scene.control.CheckBox;
import javafx.scene.control.TextField;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;

@KeYView(title = "Sequent", path = "SequentView.fxml", preferredPosition = ViewPosition.CENTER, hasMenuItem = false)

public class SequentViewController extends ViewController {

    private boolean sequentLoaded = false;
    private SequentPrinter printer;
    private LogicPrinter logicPrinter;
    private String proofString;
    private WebEngine webEngine;
    private NotationInfo notationInfo = new NotationInfo();
    private Services services;
    private Sequent sequent;
    private IProofListener proofChangeListener = (proofEvent) -> {
        // execute ui update on javafx thread
        Platform.runLater(() -> {
            showRootSequent();
        });

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
        printer = new SequentPrinter("resources/css/sequentStyle.css",
                "resources/css/sequentClasses.ini");
    }

    @Override
    public void initializeAfterLoadingFxml() {
        context.getProofManager().addProofListener(proofChangeListener);
    }

    private void initializeSearchBox() {
        String searchBoxLabel = "Search...";
        searchBox.setText(searchBoxLabel);
        searchBox.focusedProperty()
                .addListener((arg0, oldPropertyValue, newPropertyValue) -> {
                    if (newPropertyValue
                            && searchBox.getText().equals(searchBoxLabel))
                        searchBox.clear();
                    else if (searchBox.getText().isEmpty())
                        searchBox.setText(searchBoxLabel);
                });

        searchBox.setOnKeyReleased((event) -> {
            printer.setFreeTextSearch(searchBox.getText());
            updateHtml(printer.printSequent(proofString));
            event.consume();
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

        logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo,
                services);
        printSequent();

        checkBoxPrettySyntax.setDisable(false);
        checkBoxUnicode.setDisable(false);
        searchButton.setDisable(false);
    }

    /**
     * Enables/Disables Pretty Syntax.
     */
    @FXML
    private void usePrettySyntax() {
        logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo,
                services);
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
        logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo,
                services);
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
        sequentLoaded = true;
        // System.out.println(printer.escape(proofString));
        updateHtml(printer.printSequent(proofString));
    }

    /**
     * Loads a default proof and displays the sequent of its root node.
     */
    @FXML
    private void loadDefaultProof() {
        context.getProofManager()
                .loadProblem(new File("resources/proofs/gcd.closed.proof"));
        // File file = new File("resources/proofs/gcd.closed.proof");
        // mainApp.setProof(file);
        // showRootSequent();
    }

    private void updateHtml(String s) {
        webEngine = textAreaWebView.getEngine();
        webEngine.loadContent(s);    }
}
