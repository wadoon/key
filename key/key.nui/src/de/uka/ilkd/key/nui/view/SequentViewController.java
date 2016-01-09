package de.uka.ilkd.key.nui.view;

import java.io.File;
import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.Filter;
import de.uka.ilkd.key.nui.model.IProofListener;
import de.uka.ilkd.key.nui.util.IAcceptSequentFilter;
import de.uka.ilkd.key.nui.util.PositionTranslator;
import de.uka.ilkd.key.nui.util.SequentPrinter;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.scene.control.CheckBox;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.layout.Pane;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 * @author Nils Muzzulini
 *
 */
@KeYView(title = "Sequent", path = "SequentView.fxml", preferredPosition = ViewPosition.CENTER, hasMenuItem = false)
public class SequentViewController extends ViewController implements IAcceptSequentFilter {

    private boolean sequentLoaded = false;
    private SequentPrinter printer;
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
                    getContext().getProofManager().getMediator().getSelectedNode());
        });
    };
    private PositionTranslator posTranslator;

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
        posTranslator = new PositionTranslator(
                "resources/css/sequentStyle.css");

        textAreaWebView.setOnMouseMoved(event -> {
            if (sequentLoaded) {

                int pos = posTranslator.getCharIdxUnderPointer(event);
                Range range = this.abstractSyntaxTree.rangeForIndex(pos);

                this.printer.applyMouseHighlighting(range);
                this.updateView();
            }
        });
        textAreaWebView.setOnMouseExited(event -> {
            if (sequentLoaded) {
                this.printer.removeMouseHighlighting();
                this.updateView();
            }
        });
    }

    @Override
    public void initializeAfterLoadingFxml() {
        getContext().getProofManager().addProofListener(proofChangeListener);
    }

    // TODO add comments
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
            // printer.setFreeTextSearch(searchBox.getText());
            printer.applyFreetextSearch(searchBox.getText());
            updateView();
            event.consume();
        });
    }

    @FXML
    private void toggleSearch() {
        searchParent.managedProperty().bind(searchParent.visibleProperty());
        searchParent.setVisible(searchButton.isSelected());
    }

    /**
     * Displays the sequent of the currently selected node in the tree.
     * 
     * @param node
     *            The selected node.
     */
    private void showSequent(Node node) {
        Proof proof = getContext().getProofManager().getMediator()
                .getSelectedProof();
        services = proof.getServices();
        sequent = node.sequent();

        logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo,
                services);
        abstractSyntaxTree = logicPrinter.getInitialPositionTable();
        printer = new SequentPrinter("resources/css/sequentStyle.css",
                abstractSyntaxTree);

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
        printer.setProofString(proofString);

        posTranslator.setProofString(proofString);

        sequentLoaded = true;
        updateView();
    }

    /**
     * Loads a default proof and displays the sequent of its root node.
     */
    @FXML
    private void loadDefaultProof() {
        getContext().getProofManager()
                .loadProblem(new File("resources/proofs/gcd.closed.proof"));
    }

    private void updateHtml(String s) {
        webEngine = textAreaWebView.getEngine();

        // The following code prints the org.w3c.document into the console.
        // TODO remove if not needed.
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
        // int h = (int) webEngine.executeScript("document.body.scrollTop");
        webEngine.loadContent(s);

        // webEngine.executeScript("window.scrollTo(" + 0 + ", " + h + ")");
    }

    private void updateView() {
        updateHtml(this.printer.printProofString());
    }

    @Override
    public void Apply(Filter filter) {
        
    }
}
