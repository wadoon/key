package de.uka.ilkd.key.nui.view;

import java.io.IOException;
import java.net.URL;
import java.nio.file.DirectoryStream.Filter;
import java.util.ResourceBundle;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.filter.EmptyEventArgs;
import de.uka.ilkd.key.nui.filter.FilterSelection;
import de.uka.ilkd.key.nui.filter.PrintFilter;
import de.uka.ilkd.key.nui.filter.SelectModeEventArgs;
import de.uka.ilkd.key.nui.util.CssFileHandler;
import de.uka.ilkd.key.nui.util.PositionTranslator;
import de.uka.ilkd.key.nui.util.SequentPrinter;
import de.uka.ilkd.key.nui.util.TermInfoPrinter;
import de.uka.ilkd.key.nui.view.menu.TacletMenuController;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.ui.MediatorProofControl;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.geometry.Side;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TextField;
import javafx.scene.control.TitledPane;
import javafx.scene.input.MouseEvent;
import javafx.scene.input.MouseButton;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 * @author Nils Muzzulini
 *
 */
@KeYView(title = "Sequent", path = "SequentView.fxml", preferredPosition = ViewPosition.CENTER, hasMenuItem = true)
public class SequentViewController extends ViewController {

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
    private PrintFilter lastFilter = null;
    private KeYSelectionListener proofChangeListener = new KeYSelectionListener() {
        @Override
        public void selectedProofChanged(KeYSelectionEvent e) {
        }

        @Override
        public void selectedNodeChanged(KeYSelectionEvent e) {
            // execute ui update on javafx thread
            Platform.runLater(() -> {
                showSequent(getContext().getKeYMediator().getSelectedNode());
                usePrettySyntax();
                useUnicode();
                useRegex();
                if (lastFilter != null) {
                    apply(lastFilter);
                    updateView();
                }
                tacletInfoViewController.showTacletInfo(
                        getContext().getKeYMediator().getSelectedNode());

                RuleApp app = getContext().getKeYMediator().getSelectedNode()
                        .getAppliedRuleApp();
                if (app != null) {
                    printer.applyRuleAppHighlighting(app);
                    updateView();
                }
            });
        }
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
    private WebView textArea;
    @FXML
    private TextField searchBox;
    @FXML
    private ScrollPane scrollPane;
    @FXML
    private TitledPane tacletInfo;
    @FXML
    private TacletInfoViewController tacletInfoViewController;
    private ContextMenu tacletMenu;

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

        textArea.setOnMouseMoved(event -> {
            if (sequentLoaded) {

                int pos = posTranslator.getCharIdxUnderPointer(event);
                Range range = this.abstractSyntaxTree.rangeForIndex(pos);

                this.printer.applyMouseHighlighting(range);
                this.updateView();

                if (event.isAltDown()) {
                    getContext().getStatusManager()
                            .setStatus(TermInfoPrinter.printTermInfo(sequent,
                                    (abstractSyntaxTree.getPosInSequent(pos,
                                            new IdentitySequentPrintFilter(
                                                    sequent)))));
                }
            }
        });

        textArea.setOnMouseExited(event -> {
            if (sequentLoaded) {
                this.printer.removeMouseHighlighting();
                this.updateView();
                getContext().getStatusManager().clearStatus();
            }
        });

        textArea.setOnMouseClicked(event -> {
            if (sequentLoaded && event.getButton() == MouseButton.PRIMARY) {
                if (tacletMenu != null)
                    tacletMenu.hide();

                // XXX loading context menus should get static method in

                FXMLLoader loader = new FXMLLoader();
                loader.setLocation(TacletMenuController.class
                        .getResource("TacletMenu.fxml"));
                try {
                    tacletMenu = loader.load();
                    // Give the controller access to the main app.
                    TacletMenuController controller = loader.getController();
                    controller.setMainApp(this.getMainApp(), this.getContext());

                    KeYMediator mediator = getContext().getKeYMediator();

                    Goal goal = mediator.getSelectedGoal();
                    if (goal != null) {
                        MediatorProofControl c = mediator.getUI()
                                .getProofControl();
                        int idx = posTranslator.getCharIdxUnderPointer(event);
                        PosInSequent pos = abstractSyntaxTree.getPosInSequent(
                                idx, new IdentitySequentPrintFilter(sequent));
                        PosInOccurrence occ = pos.getPosInOccurrence();
                        final ImmutableList<BuiltInRule> builtInRules = c
                                .getBuiltInRule(goal, occ);
                        controller.init(c.getFindTaclet(goal, occ),
                                c.getRewriteTaclet(goal, occ),
                                c.getNoFindTaclet(goal), builtInRules, pos);

                        tacletMenu.show(textArea, Side.TOP, event.getX(),
                                event.getY());
                    }
                }
                catch (IOException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
            }
        });

        textArea.setOnScroll(event -> {
            // Adjustment: Event.getDelta is absolute amount of pixels,
            // Scrollpane.getHvalue and .getVvalue relative from 0.0 to 1.0
            this.scrollPane.setVvalue(
                    this.scrollPane.getVvalue() - event.getDeltaY() / 800);
            this.scrollPane.setHvalue(this.scrollPane.getHvalue()
                    - event.getDeltaX() / this.scrollPane.getWidth());
        });

        textArea.setOnMouseClicked(this::handleWebViewClicked);
    }

    @Override
    public void initializeAfterLoadingFxml() {
        getContext().getKeYMediator()
                .addKeYSelectionListener(proofChangeListener);
        getContext().getFilterChangedEvent().addHandler(this::apply);
        getContext().getSelectModeActivateEvent()
                .addHandler(this::selectModeActivated);

        posTranslator = new PositionTranslator(
                getContext().getCssFileHandler());

        tacletInfoViewController.setMainApp(getMainApp(), getContext());
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
        Proof proof = getContext().getKeYMediator().getSelectedProof();
        services = proof.getServices();
        sequent = node.sequent();

        logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo,
                services);
        abstractSyntaxTree = logicPrinter.getInitialPositionTable();
        printer = new SequentPrinter(getContext().getCssFileHandler().getCss(),
                abstractSyntaxTree, getContext());
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

        printer.setPosTable(abstractSyntaxTree);
        printer.setSequent(sequent);
        printer.setProofString(proofString);

        posTranslator.setProofString(proofString);

        sequentLoaded = true;
        updateView();
    }

    private void updateHtml(String s) {
        webEngine = textArea.getEngine();
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

            // JavaFX 8 has MaxHeight 8192. If bigger, an error will occur.
            // Shall be patched in JDK9
            if (newHeight > 8192) {
                System.out.println(
                        "Proof might be too large with Size " + newHeight);
                textArea.setPrefHeight(8192);
            }
            else {
                textArea.setPrefHeight(newHeight);
            }
            textArea.autosize();
        }

        updateHtml(this.printer.printProofString());
    }

    private void apply(PrintFilter filter) {
        lastFilter = filter;
        printer.applyFilter(filter);
        posTranslator.applyFilter(filter);
        updateView();
    }

    boolean selectionModeIsActive = false;
    private FilterSelection filterSelection;

    private void selectModeActivated(SelectModeEventArgs eventArgs) {
        filterSelection = eventArgs.getFilterSelection();
        filterSelection.getSelectionModeFinishedEvent()
                .addHandler(this::finishSelectionMode);
        selectionModeIsActive = true;
    }

    public void finishSelectionMode(EmptyEventArgs args) {
        for (Range range : filterSelection.getSelection())
            this.printer.removeSelection(range);
        filterSelection.createCriteria(proofString);
        updateView();
    }

    private void handleWebViewClicked(MouseEvent event) {
        if (sequentLoaded && selectionModeIsActive) {
            int pos = posTranslator.getCharIdxUnderPointer(event);
            Range range = this.abstractSyntaxTree.rangeForIndex(pos);

            if (filterSelection.tryAddRange(range)) {
                this.printer.applySelection(range);
            }
            else {
                this.printer.removeSelection(range);
            }
            this.updateView();
            /*
             * if (event.isAltDown())
             * showTermInfo(abstractSyntaxTree.getPosInSequent(pos, new
             * IdentitySequentPrintFilter(sequent)));
             */
        }
    }
}
