package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.PrintFilter;
import de.uka.ilkd.key.nui.model.IProofListener;
import de.uka.ilkd.key.nui.util.IAcceptSequentFilter;
import de.uka.ilkd.key.nui.util.PositionTranslator;
import de.uka.ilkd.key.nui.util.SequentPrinter;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TextField;
import javafx.scene.control.TitledPane;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;
import javafx.util.Pair;

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
    private TacletInfoViewController tacletInfoVC;
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
            tacletInfoVC.showTacletInfo(getContext().getProofManager()
                    .getMediator().getSelectedNode());
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
    @FXML
    private TitledPane tacletInfo;

    /**
     * The constructor. The constructor is called before the initialize()
     * method.
     */
    public SequentViewController() {

    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        initializeSearchBox();
        tacletInfo.setDisable(true);
        tacletInfo.setExpanded(false);

        sequentOptions.setDisable(true);
        sequentOptions.setExpanded(false);
        sequentOptions.expandedProperty()
                .addListener((observable, oldValue, newValue) -> {
                    if (sequentOptions.isExpanded()) {
                        sequentOptions.setText("Less Options");
                    }
                    else {
                        sequentOptions.setText("More Options");
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

                if (event.isAltDown())
                    showTermInfo(abstractSyntaxTree.getPosInSequent(pos,
                            new IdentitySequentPrintFilter(sequent)));
            }
        });
        
        textAreaWebView.setOnMouseExited(event -> {
            if (sequentLoaded) {
                this.printer.removeMouseHighlighting();
                this.updateView();
                getContext().getStatusManager().clearStatus();
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

    private void showTermInfo(PosInSequent pos) {
        String info = null;
        Term t;
        if (pos != null) {
            PosInOccurrence occ = pos.getPosInOccurrence();
            if (occ != null) {
                t = occ.subTerm();
                String tOpClassString = t.op().getClass().toString();
                String operator = tOpClassString
                        .substring(tOpClassString.lastIndexOf('.') + 1);
                // The hash code is displayed here since sometimes terms with
                // equal string representation are still different.
                info = operator + ", Sort: " + t.sort() + ", Hash: "
                        + t.hashCode();

                info += ProofSaver.posInOccurrence2Proof(sequent, occ);
                getContext().getStatusManager().setStatus(info);
            }
        }  
    }

    @Override
    public void initializeAfterLoadingFxml() {
        getContext().getProofManager().addProofListener(proofChangeListener);
        // XXX see FilterView
        getContext().registerFilterConsumer(this);

        Pair<Object, ViewController> p = loadFxmlViewController(
                getClass().getResource("TacletInfoView.fxml"));
        tacletInfoVC = (TacletInfoViewController) p.getValue();
        tacletInfo.setContent((javafx.scene.Node) p.getKey());
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

        searchBox.setOnKeyReleased(event -> {
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
        tacletInfo.setDisable(false);
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
        webEngine.loadContent(s);
    }

    private void updateView() {
        // Redraw WebArea to use optimal Height. Called here as PosTranslater
        // needs to know the ProofString.
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
    public void apply(PrintFilter filter) {
        printer.applyFilter(filter);
        posTranslator.applyFilter(filter);
        updateView();
    }
}
