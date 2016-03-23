package de.uka.ilkd.key.nui.view;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;
import java.util.ResourceBundle;
import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.event.EmptyEventArgs;
import de.uka.ilkd.key.nui.filter.FilterChangedEventArgs;
import de.uka.ilkd.key.nui.filter.FilterSelection;
import de.uka.ilkd.key.nui.filter.PrintFilter.FilterLayout;
import de.uka.ilkd.key.nui.filter.SelectModeEventArgs;
import de.uka.ilkd.key.nui.filter.SequentFilterer;
import de.uka.ilkd.key.nui.printer.SequentPrinter;
import de.uka.ilkd.key.nui.printer.TermInfoPrinter;
import de.uka.ilkd.key.nui.util.PositionTranslator;
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
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Pair;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TextField;
import javafx.scene.control.TitledPane;
import javafx.scene.control.Tooltip;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.MouseButton;
import javafx.scene.input.MouseEvent;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 * @author Nils Muzzulini
 *
 */
public class SequentViewController extends ViewController {
    // For StaticSequentView Synchronization
    private static AtomicLong NEXT_ID = new AtomicLong(0);
    private final long OWN_ID = NEXT_ID.getAndIncrement();
    private static AtomicLong LAST_TACLET_ACTION_ID;

    private boolean sequentLoaded = false;
    private boolean sequentChanged = false;
    private SequentPrinter printer;
    private LogicPrinter logicPrinter;
    private InitialPositionTable abstractSyntaxTree;
    private String proofString;
    private WebEngine webEngine;
    private NotationInfo notationInfo;
    private Services services;
    private Sequent sequent;
    private FilterChangedEventArgs lastFilter = null;
    private PositionTranslator posTranslator;
    private List<Integer> searchIndices;
    private int searchIndPointer = 0;
    private String formerSearchText = "";

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
        if (LAST_TACLET_ACTION_ID == null) {
            LAST_TACLET_ACTION_ID = new AtomicLong(-1);
        }
    }

    public long getOwnID() {
        return OWN_ID;
    }

    public long getLastTacletActionID() {
        return LAST_TACLET_ACTION_ID.get();
    }

    public void setLastTacletActionID(long newValue) {
        LAST_TACLET_ACTION_ID.set(newValue);
    }

    public void loadNodeToView(Node node) {
        showSequent(node);
        tacletInfoViewController.showTacletInfo(node);
        notationInfo.refresh(services, checkBoxPrettySyntax.isSelected(),
                checkBoxUnicode.isSelected());
        useRegex();
        printSequent();
        RuleApp app = node.getAppliedRuleApp();
        if (lastFilter != null) {
            apply(lastFilter);
        }
        if (app != null) {
            printer.applyRuleAppHighlighting(app);
        }

        searchIndices = null;
        searchIndPointer = 0;
        formerSearchText = "";

        updateView();
    }

    public String getProofString() {
        return proofString;
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        initializeSearchBox();
        tacletInfo.setDisable(true);
        tacletInfo.setExpanded(false);
        enableTacletMenu(true);

        sequentOptions.setDisable(true);
        sequentOptions.setExpanded(false);
        sequentOptions.disabledProperty()
                .addListener((observable, oldValue, newValue) -> {
                    sequentOptions.getScene()
                            .getAccelerators().put(
                                    new KeyCodeCombination(KeyCode.F,
                                            KeyCombination.CONTROL_DOWN),
                                    () -> {
                        if (sequentOptions.isExpanded()
                                && !searchBox.isFocused()) {
                            searchBox.requestFocus();
                            return;
                        }
                        sequentOptions.setAnimated(false);
                        sequentOptions
                                .setExpanded(!sequentOptions.isExpanded());
                        searchBox.requestFocus();
                        sequentOptions.setAnimated(true);
                    });
                });

        // Disable the standard context menu, as it only offers a page refresh,
        // which is not needed.
        textArea.setContextMenuEnabled(false);
        textArea.setOnMouseClicked(this::handleWebViewClicked);

        textArea.setOnScroll(event -> {
            // Adjustment: Event.getDelta is absolute amount of pixels,
            // Scrollpane.getHvalue and .getVvalue relative from 0.0 to 1.0
            this.scrollPane.setVvalue(this.scrollPane.getVvalue()
                    - event.getDeltaY() / this.scrollPane.getHeight());
            this.scrollPane.setHvalue(this.scrollPane.getHvalue()
                    - event.getDeltaX() / this.scrollPane.getWidth());
        });
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void setTooltips() {
        checkBoxRegexSearch
                .setTooltip(new Tooltip("Evaluate as regular expression."));
        checkBoxPrettySyntax.setTooltip(
                new Tooltip("If ticked, infix notations are used."));
        checkBoxUnicode.setTooltip(new Tooltip(
                "If ticked, formulae are displayed with special Unicode characters (such as `\u22C0`) instead of the traditional ASCII ones. "
                        + "Only works in combination with pretty printing (see above)."));
    }

    // XXX kind of a hack
    private void enableMouseOver(boolean enable) {

        if (enable) {
            textArea.setOnMouseMoved(this::handleTextAreaMouseMoved);
            textArea.setOnMouseExited(this::handleTextAreaMouseExited);
        }
        else {
            textArea.setOnMouseMoved(null);
            textArea.setOnMouseExited(null);
        }
    }

    private void handleTextAreaMouseMoved(MouseEvent event) {

        int pos = posTranslator.getCharIdxUnderPointer(event);
        Range range = this.abstractSyntaxTree.rangeForIndex(pos);

        this.printer.applyMouseHighlighting(range);
        this.updateView();

        if (event.isAltDown()) {
            getContext().getStatusManager()
                    .setStatus(TermInfoPrinter.printTermInfo(sequent,
                            (abstractSyntaxTree.getPosInSequent(pos,
                                    new IdentitySequentPrintFilter(sequent)))));
        }
    }

    private void handleTextAreaMouseExited(MouseEvent event) {
        this.printer.removeMouseHighlighting();
        this.updateView();
        if (event.isAltDown()) {
            getContext().getStatusManager().resetStatus();
        }
    }

    @Override
    public void initializeAfterLoadingFxml() {
        notationInfo = getContext().getKeYMediator().getNotationInfo();
        getContext().getFilterChangedEvent().addHandler(eventArgs -> {
            if (getContext().getKeYMediator().getSelectedProof() == null)
                return;
            apply(eventArgs);
            updateView();
        });
        getContext().getSelectModeActivateEvent()
                .addHandler(this::selectModeActivated);

        posTranslator = new PositionTranslator(
                getContext().getCssFileHandler());

        tacletInfoViewController.initViewController(getMainApp(), getContext());
    }

    /**
     * initializes the Searchbox: registers all the Event behavior
     */
    private void initializeSearchBox() {
        searchBox.setOnKeyReleased(event -> {
            // Ignore Regex with "."
            if (searchBox.getText().equals(".")
                    && checkBoxRegexSearch.isSelected()) {
                printer.applyFreetextSearch("");
                updateView();
                event.consume();
                return;
            }

            // Jump to Next Search Highlight if Searchtext is not Changed
            if (formerSearchText.equals(searchBox.getText())
                    && event.getCode() == KeyCode.ENTER && searchIndices != null
                    && searchIndices.size() > 0
                    && sequentOptions.isExpanded()) {

                double searchedHeight = posTranslator
                        .getHeightForIndex(searchIndices.get(searchIndPointer));

                // While the Next Highlight is in a Collapsed Line, jump to next
                // or return if it is the last line
                while (searchedHeight == -1) {
                    searchIndPointer++;
                    if (searchIndPointer == searchIndices.size()) {
                        return;
                    }
                    searchedHeight = posTranslator.getHeightForIndex(
                            searchIndices.get(searchIndPointer));
                }

                // Scroll to the next Search Highlight
                scrollPane.setVvalue(searchedHeight / scrollPane.getHeight());
                event.consume();
                searchIndPointer = (++searchIndPointer % searchIndices.size());
                return;
            }

            // Search
            formerSearchText = searchBox.getText();
            searchIndices = printer.applyFreetextSearch(searchBox.getText());
            searchIndPointer = 0;
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
        printer = new SequentPrinter(getContext().getCssFileHandler(),
                abstractSyntaxTree, getContext());
        sequentChanged = true;

        sequentOptions.setDisable(false);
        tacletInfo.setDisable(false);
        textArea.setDisable(false);
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
        }
        else {
            notationInfo.refresh(services, true, false);
            checkBoxUnicode.setDisable(false);
        }
        sequentChanged = true;
        printSequent();
        updateView();
    }

    /**
     * 
     * Enables/Disables Unicode.
     */
    @FXML
    private void useUnicode() {
        logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo,
                services);
        abstractSyntaxTree = logicPrinter.getInitialPositionTable();
        notationInfo.refresh(services, true, checkBoxUnicode.isSelected());

        sequentChanged = true;
        printSequent();
        updateView();
    }

    /**
     * Enables/Disables Regex Search
     */
    @FXML
    private void useRegex() {
        printer.setUseRegex(checkBoxRegexSearch.isSelected());
    }

    /**
     * Forces the creation of a new LogicPrinter and syntax tree and reloads the
     * webview. Use this after changes of the NotationInfo of the mediator.
     */
    public void forceRefresh() {
        logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo,
                services);
        abstractSyntaxTree = logicPrinter.getInitialPositionTable();
        printSequent();
        updateView();
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
        if (!sequentLoaded) {
            sequentLoaded = true;
            enableMouseOver(true);
        }
    }

    private void updateHtml(String s) {
        webEngine = textArea.getEngine();
        webEngine.loadContent(s);
    }

    public void updateView() {
        // Redraw WebArea to use optimal Height. Called here as PosTranslater
        // needs to know the ProofString.
        // If-clause added for optimization purposes. Only when the Sequent
        // itself is changed, the WebArea needs to be redrawn, not with every
        // styling update.
        if (sequentChanged && sequentLoaded) {
            sequentChanged = false;
            Pair<Double, Double> newDimensions = posTranslator
                    .getProofDimensions();

            // JavaFX 8 has MaxHeight 8192. If bigger, an error will occur.
            // Shall be patched in JDK9
            if (newDimensions.second > 8192) {
                System.out.println("Proof might be too large with Size "
                        + newDimensions.second);
                textArea.setPrefHeight(8192);
            }
            else {
                textArea.setPrefHeight(newDimensions.second);
            }

            textArea.setPrefWidth(newDimensions.first);
            textArea.autosize();
        }

        updateHtml(this.printer.printProofString());
    }

    private void apply(FilterChangedEventArgs args) {
        if (!sequentLoaded)
            return;
        lastFilter = args;

        ArrayList<Integer> lines = new ArrayList<Integer>(
                SequentFilterer.applyFilter(proofString, args.getFilter(),
                        abstractSyntaxTree));

        if (args.getFilter() != null) {
            printer.applyFilter(lines, args.getFilter().getFilterLayout());
            posTranslator.applyFilter(lines,
                    args.getFilter().getFilterLayout());
        }
        else {
            // filter layout does not matter here, but can't be acquired from
            // the filter
            printer.applyFilter(lines, FilterLayout.Minimize);
            posTranslator.applyFilter(lines, FilterLayout.Minimize);
        }
    }

    boolean selectionModeIsActive = false;
    private FilterSelection filterSelection;
    private boolean enableTacletMenu;

    private void selectModeActivated(SelectModeEventArgs eventArgs) {
        if (getContext().getKeYMediator().getSelectedProof() == null)
            return;
        filterSelection = eventArgs.getFilterSelection();
        filterSelection.getSelectionModeFinishedEvent()
                .addHandler(this::finishSelectionMode);
        selectionModeIsActive = true;
    }

    public void finishSelectionMode(EmptyEventArgs args) {
        for (Range range : filterSelection.getSelection())
            this.printer.removeSelection(range);
        filterSelection.resolveSelection(proofString);
        updateView();
        selectionModeIsActive = false;
    }

    private void handleWebViewClicked(MouseEvent event) {
        if (!sequentLoaded || event.getButton() != MouseButton.PRIMARY)
            return;

        if (selectionModeIsActive) {
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
        else {
            if (tacletMenu != null)
                tacletMenu.hide();
            else {
                if (!enableTacletMenu)
                    return;
                try {
                    // XXX loader stuff should be moved
                    // XXX menu should only be loaded once
                    KeYMediator mediator = getContext().getKeYMediator();

                    Goal goal = mediator.getSelectedGoal();
                    if (goal != null) {
                        int idx = posTranslator.getCharIdxUnderPointer(event);
                        PosInSequent pos = abstractSyntaxTree.getPosInSequent(
                                idx, new IdentitySequentPrintFilter(sequent));

                        if (pos == null)
                            return;

                        FXMLLoader loader = new FXMLLoader();
                        loader.setLocation(TacletMenuController.class
                                .getResource("TacletMenu.fxml"));
                        tacletMenu = loader.load();
                        // Give the controller access to the main app.
                        TacletMenuController controller = loader
                                .getController();
                        controller.initViewController(this.getMainApp(),
                                this.getContext());
                        controller.init(pos, this);

                        tacletMenu.show(textArea, event.getScreenX(),
                                event.getScreenY());

                        enableMouseOver(false);

                        // Used for StaticSequentView Synchro
                        setLastTacletActionID(OWN_ID);

                        tacletMenu.setOnHiding(evt -> {
                            enableMouseOver(true);
                            tacletMenu = null;
                        });
                    }
                }
                catch (IOException e) {
                    e.printStackTrace();
                    System.err.print("Could not load TacletMenu.\n");
                }
            }
        }
    }

    public void enableTacletMenu(boolean enable) {
        enableTacletMenu = enable;

    }

    protected void clearWebView() {
        sequentOptions.setDisable(true);
        tacletInfo.setDisable(true);
        textArea.setDisable(true);
        webEngine.load("");
    }
}
