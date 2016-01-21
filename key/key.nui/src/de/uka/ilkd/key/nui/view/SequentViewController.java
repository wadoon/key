package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.PrintFilter;
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
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.fxml.FXML;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TextField;
import javafx.scene.control.TitledPane;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 * @author Nils Muzzulini
 *
 */
@KeYView(title = "Sequent", path = "SequentView.fxml", preferredPosition = ViewPosition.CENTER, hasMenuItem = true)
public class SequentViewController extends ViewController
        implements IAcceptSequentFilter {

    private boolean sequentLoaded = false;
    private boolean sequentChanged = false;
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
            showSequent(getContext().getProofManager().getMediator()
                    .getSelectedNode());
        });
    };
    private PositionTranslator posTranslator;
    
    @FXML
    private TitledPane sequentOptions;
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
    @FXML
    private ScrollPane scrollPane;

    /**
     * The constructor. The constructor is called before the initialize()
     * method.
     */
    public SequentViewController() {
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        initializeSearchBox();
        sequentOptions.setDisable(true);
        sequentOptions.setExpanded(false);
        sequentOptions.expandedProperty().addListener(new ChangeListener<Boolean>() {
            @Override
            public void changed(ObservableValue<? extends Boolean> observable, Boolean oldValue, Boolean newValue) {
                if (sequentOptions.isExpanded()) {
                    sequentOptions.setText("Less Options");
                } else {
                    sequentOptions.setText("More Options");
                }
            }
        });
        
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

        textAreaWebView.setOnScroll(event -> {
            // Adjustment: Event.getDelta is absolute amount of pixels,
            // Scrollpane.getHvalue and .getVvalue relative from 0.0 to 1.0
            this.scrollPane.setVvalue(
                    this.scrollPane.getVvalue() - event.getDeltaY() / 800);
            this.scrollPane.setHvalue(this.scrollPane.getHvalue()
                    - event.getDeltaX() / this.scrollPane.getWidth());
        });

    }

    @Override
    public void initializeAfterLoadingFxml() {
        getContext().getProofManager().addProofListener(proofChangeListener);
        // XXX see FilterView
        getContext().registerFilterConsumer(this);
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

        sequentChanged = true;

        printSequent();
        
        sequentOptions.setDisable(false);
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
        // Redraw WebArea to use optimal Height. Called here as PosTranslater
        // needs to now the ProofString.
        // If-clause added for optimization purposes. Only when the Sequent
        // itself is changed, the WebArea needs to be redrawn, not with every
        // styling update.

        if (sequentChanged && sequentLoaded) {
            sequentChanged = false;
            double newHeight = posTranslator.getProofHeight();

            // JavaFX has MaxHeight ~8500. If bigger, an error might occur.
            if (newHeight > 8500) {
                System.out.println("Proof might be too large");
                textAreaWebView.setPrefHeight(8500);
            }
            else {
                textAreaWebView.setPrefHeight(newHeight);
            }
            textAreaWebView.autosize();
        }

        updateHtml(this.printer.printProofString());
    }

    @Override
    public void Apply(PrintFilter filter) {
        printer.applyFilter(filter);
        posTranslator.applyFilter(filter);
        updateView();
    }
}
