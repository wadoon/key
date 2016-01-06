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
import de.uka.ilkd.key.nui.util.PositionConverter;
import de.uka.ilkd.key.nui.util.SequentPrinter;
import de.uka.ilkd.key.nui.util.SequentPrinterCorrected;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import javafx.application.Platform;
<<<<<<< HEAD
import javafx.fxml.FXML;
=======
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.concurrent.Worker;
import javafx.concurrent.Worker.State;
import javafx.embed.swing.SwingNode;
>>>>>>> 3ceaaac237d16ec19172d2f39e5a3bd4b8d4c841
import javafx.scene.control.CheckBox;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.layout.Pane;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;

@KeYView(title = "Sequent", path = "SequentView.fxml", preferredPosition = ViewPosition.CENTER, hasMenuItem = false)
public class SequentViewController extends ViewController {

    private boolean sequentLoaded = false;
    private SequentPrinter printer;
    private SequentPrinterCorrected printerCorrected;
    private LogicPrinter logicPrinter;
    private InitialPositionTable abstractSyntaxTree;
    private String proofString;
    private WebEngine webEngine;
    private NotationInfo notationInfo = new NotationInfo();
    private Services services;
    private Sequent sequent;
    private IProofListener proofChangeListener = (proofEvent) -> {
        // execute ui update on javafx thread
        Platform.runLater(() -> {
            showSequent(
                    context.getProofManager().getMediator().getSelectedNode());
        });
    };
    private PositionConverter posConverter;

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
        textAreaWebView.setOnMouseMoved(event -> {
            if (sequentLoaded) {

                int pos = posConverter.getCharIdxUnderPointer(event);
                Range range = this.abstractSyntaxTree.rangeForIndex(pos);
                // String highlighted =
                // this.printer.highlightString(proofString, range.start(),
                // range.end()-range.start());
                System.out.println("POS: " + pos);
                System.out.println("RANGE: " + range);
                this.printerCorrected.applyMouseHighlighting(range);
                this.updateHtml(this.printerCorrected.printProofString());
                System.out.println();
            }
        });
        textAreaWebView.setOnMouseExited(event -> {
            if (sequentLoaded) {
                this.printerCorrected.removeMouseHighlighting();
                this.updateHtml(this.printerCorrected.printProofString());
            }
        });
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

    private void showSequent(Node node) {
        Proof proof = context.getProofManager().getMediator()
                .getSelectedProof();
        services = proof.getServices();
        sequent = node.sequent();

        logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo,
                services);
        abstractSyntaxTree = logicPrinter.getInitialPositionTable();
        printerCorrected = new SequentPrinterCorrected(
                "resources/css/sequentStyle.css", abstractSyntaxTree);

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
        abstractSyntaxTree = logicPrinter.getInitialPositionTable();
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
        abstractSyntaxTree = logicPrinter.getInitialPositionTable();
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
        printerCorrected.setProofString(proofString);

        posConverter = new PositionConverter(proofString);

        sequentLoaded = true;
        updateHtml(printerCorrected.printProofString());
    }

    /**
     * Loads a default proof and displays the sequent of its root node.
     */
    @FXML
    private void loadDefaultProof() {
        context.getProofManager()
                .loadProblem(new File("resources/proofs/gcd.closed.proof"));
    }

    private void updateHtml(String s) {
        webEngine = textAreaWebView.getEngine();

        /*
         * webEngine.getLoadWorker().stateProperty().addListener( new
         * ChangeListener<State>() { public void changed(ObservableValue ov,
         * State oldState, State newState) { if (newState ==
         * Worker.State.SUCCEEDED) { Document doc = webEngine.getDocument(); try
         * { Transformer transformer =
         * TransformerFactory.newInstance().newTransformer();
         * transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "no");
         * transformer.setOutputProperty(OutputKeys.METHOD, "xml");
         * transformer.setOutputProperty(OutputKeys.INDENT, "yes");
         * transformer.setOutputProperty(OutputKeys.ENCODING, "UTF-8");
         * transformer.setOutputProperty(
         * "{http://xml.apache.org/xslt}indent-amount", "4");
         * 
         * transformer.transform(new DOMSource(doc), new StreamResult(new
         * OutputStreamWriter(System.out, "UTF-8"))); } catch (Exception ex) {
         * ex.printStackTrace(); } } } });
         */

        webEngine.loadContent(s);
    }

    @Override
    public void createSwingContent(SwingNode swingNode) {
        // TODO Auto-generated method stub
        
    }
}
