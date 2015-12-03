package de.uka.ilkd.key.nui.view;

import java.io.File;
import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.java.Services;
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
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.scene.control.ToggleButton;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.Pane;
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

    // @FXML
    // private TextArea textArea;

    @FXML
    private CheckBox checkBoxPrettySyntax;

    @FXML
    private CheckBox checkBoxUnicode;

    @FXML
    private WebView textAreaWebView;

    @FXML
    private ToggleButton filterButton;

    @FXML
    private Pane filterParent;

    @FXML
    private TextField filterText;

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
        // hide the filter at the beginning
        toggleFilter();
        initializeSearchBox();
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

    /**
     * After a proof has been loaded, the sequent of the root node will be
     * displayed
     */
    @FXML
    private void showRootSequent() {
        Proof proof = mainApp.getProof();
        if (proof == null) {
            mainApp.setStatus("Please Select a Proof first.");
            return;
        }
        services = proof.getServices();
        Node node = proof.root();
        sequent = node.sequent();

        logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo, services);
        notationInfo.refresh(services, false, false);
        printSequent();

        // textAreaWebView.setOnMouseMoved(mousehandler);
    }

    /**
     * Enables/Disables Pretty Syntax. Only works when a sequent is displayed.
     */
    @FXML
    private void usePrettySyntax() {
        if (!sequentLoaded) {
            mainApp.setStatus("Please load and diplay a proof first.");
            checkBoxPrettySyntax.setSelected(false);
            return;
        }
        else if (notationInfo.isPrettySyntax()) {
            logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo, services);
            notationInfo.refresh(services, false, false);
            checkBoxPrettySyntax.setSelected(false);
            checkBoxUnicode.setSelected(false);
            printSequent();
            return;
        }
        else {
            logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo, services);
            notationInfo.refresh(services, true, false);
            checkBoxPrettySyntax.setSelected(true);
            printSequent();
        }
    }

    /**
     * Enables/Disables Unicode. Only works when a sequent is displayed and
     * Pretty Syntax is enabled.
     */
    @FXML
    private void useUnicode() {
        if (!notationInfo.isPrettySyntax() || !sequentLoaded) {
            mainApp.setStatus("Please enable Pretty Syntax first.");
            checkBoxUnicode.setSelected(false);
            return;
        }
        else if (notationInfo.isUnicodeEnabled()) {
            logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo, services);
            notationInfo.refresh(services, true, false);
            checkBoxUnicode.setSelected(false);
            printSequent();
            return;
        }
        else {
            logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo, services);
            notationInfo.refresh(services, true, true);
            checkBoxUnicode.setSelected(true);
            printSequent();
        }
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
        File file = new File("resources/proofs/gcd.closed.proof");
        mainApp.setProof(file);
        showRootSequent();
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

    @FXML
    private void toggleFilter() {
        filterParent.managedProperty().bind(filterParent.visibleProperty());
        filterParent.setVisible(filterButton.isSelected());
    }

    private void updateHtml(String s) {
        webEngine = textAreaWebView.getEngine();
        webEngine.loadContent(s);

        // textAreaWebView.getEngine().loadContent(s);
    }

    @FXML
    private void handleApplyFilter() {
        doFilter(filterText.getText());
    }

    // just dummy method
    private void doFilter(String filterstring) {
        if (!sequentLoaded)
            return;
        printer.addTempCss("filterCss", String.format(".content %s * {display: none !important;}", filterstring));
        updateHtml(printer.printSequent(proofString));
    }
}
