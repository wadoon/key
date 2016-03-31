package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.List;
import java.util.Observable;
import java.util.Observer;
import java.util.ResourceBundle;
import java.util.function.Consumer;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.event.EmptyEventArgs;
import de.uka.ilkd.key.nui.filter.FilterSelection;
import de.uka.ilkd.key.nui.filter.PrintFilter;
import de.uka.ilkd.key.nui.filter.PrintFilter.DisplayScope;
import de.uka.ilkd.key.nui.filter.PrintFilter.FilterLayout;
import de.uka.ilkd.key.nui.util.NUIConstants;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;
import javafx.scene.control.RadioButton;
import javafx.scene.control.Slider;
import javafx.scene.control.Spinner;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.Pane;

/**
 * The view for a filter on the {@link SequentView}
 * 
 * @author Benedikt Gross
 * @version 1.0
 */
@KeYView(title = "Filter", path = "FilterView.fxml", preferredPosition = ViewPosition.BOTTOMLEFT)
public class FilterViewController extends ViewController {

    private PrintFilter currentFilter;

    @FXML
    private TextField searchText;

    @FXML
    private Slider linesBefore;

    @FXML
    private Spinner<Integer> beforeNumber;

    @FXML
    private Slider linesAfter;

    @FXML
    private Spinner<Integer> afterNumber;

    @FXML
    private CheckBox invertFilter;

    @FXML
    private ComboBox<FilterLayout> filterModeBox;

    @FXML
    private ToggleButton selectionFilterToggle;

    @FXML
    private RadioButton userRadio;

    @FXML
    private RadioButton selectionRadio;

    @FXML
    private ToggleButton applyButton;

    @FXML
    private RadioButton useAstScope;

    @FXML
    private RadioButton useTextScope;

    @FXML
    private RadioButton useNone;

    @FXML
    private Pane resultRangeText;

    @FXML
    private Label selectionCount;

    @FXML
    private Pane filterContainer;

    @FXML
    private Pane filterSettings;

    private FilterSelection filterSelection;
    private boolean suppressValueUpdate = false;
    private boolean suppressUsedFilterUpdates = false;
    private boolean ongoingSelection = false;

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        // style
        selectionFilterToggle.setStyle("-fx-background-image: url('"
                + NUIConstants.FILTER_MOUSE_ICON_PATH + "');"
                + "-fx-background-position: center center;"
                + "-fx-background-repeat: no-repeat;"
                + "-fx-background-size: contain;");
        
        // ui trigger
        searchText.disableProperty().bind(userRadio.selectedProperty().not());
        selectionFilterToggle.disableProperty()
                .bind(selectionRadio.selectedProperty().not());
        resultRangeText.disableProperty()
                .bind(useTextScope.selectedProperty().not());
        invertFilter.disableProperty()
                .bind(useAstScope.selectedProperty().not());
        beforeNumber.getEditor().textProperty()
                .addListener((o, old_val, new_val) -> {
                    updateRangeValue(linesBefore, beforeNumber,
                            currentFilter::setBefore);
                });
        afterNumber.getEditor().textProperty()
                .addListener((o, old_val, new_val) -> {
                    updateRangeValue(linesAfter, afterNumber,
                            currentFilter::setAfter);
                });
        linesBefore.valueProperty().addListener((o, old_val, new_val) -> {
            if (!suppressValueUpdate)
                beforeNumber.getValueFactory().setValue(new_val.intValue());
        });
        linesAfter.valueProperty().addListener((o, old_val, new_val) -> {
            if (!suppressValueUpdate)
                afterNumber.getValueFactory().setValue(new_val.intValue());
        });
        searchText.textProperty().addListener(
                (o, old_val, new_val) -> currentFilter.setSearchText(new_val));
        filterModeBox.valueProperty().addListener((o, old_val, new_val) -> {
            currentFilter.setFilterLayout(new_val);
        });
        userRadio.selectedProperty().addListener(this::userRadioChanged);
        selectionRadio.selectedProperty()
                .addListener(this::selectionRadioChanged);
        applyButton.selectedProperty()
                .addListener(event -> handleApplyIsSelectedChanged());

        // default data
        filterModeBox.getItems().add(FilterLayout.Collapse);
        filterModeBox.getItems().add(FilterLayout.Minimize);
        applyButton.setDisable(true);
        filterSettings.setDisable(true);

        currentFilter = new PrintFilter();
        loadCurrentFilterToUi();
    }

    @Override
    public void initializeAfterLoadingFxml() {
        getContext().getKeYMediator()
                .addKeYSelectionListener(new KeYSelectionListener() {
                    @Override
                    public void selectedProofChanged(KeYSelectionEvent e) {
                        Platform.runLater(() -> {
                            applyButton.setDisable(!getContext()
                                    .getKeYMediator().ensureProofLoaded());
                            filterSettings.setDisable(!getContext()
                                    .getKeYMediator().ensureProofLoaded());
                            if (ongoingSelection)
                                finishSelection();
                        });
                    }

                    @Override
                    public void selectedNodeChanged(KeYSelectionEvent e) {
                    }
                });
    };

    @FXML
    private void hanldeInvertChanged() {
        currentFilter.setInvert(invertFilter.isSelected());
    }

    @FXML
    private void handleScopeSelectionChanged() {
        if (useNone.isSelected())
            currentFilter.setScope(DisplayScope.None);
        else if (useAstScope.isSelected())
            currentFilter.setScope(DisplayScope.AST);
        else if (useTextScope.isSelected())
            currentFilter.setScope(DisplayScope.Text);
    }

    @FXML
    private void handleApplyIsSelectedChanged() {
        if (applyButton.isSelected()) {
            if (ongoingSelection) {
                finishSelection();
            }
            updateUsedFilter();
            applyButton.setText("Remove Filter");
        }
        else {
            getContext().setCurrentFilter(null);
            updateSelectionCount(0);
            applyButton.setText("Apply Filter");
        }
    }

    @FXML
    private void handleSelectionFilterToggled() {
        if (selectionFilterToggle.isSelected()) {
            // reset old filter to make selection more easily
            suppressUsedFilterUpdates = true;
            applyButton.setDisable(true);
            getContext().setCurrentFilter(null);
            filterSelection = new FilterSelection();
            ongoingSelection = true;
            getContext().activateSelectMode(filterSelection);
        }
        else {
            finishSelection();
            updateUsedFilter();
            applyButton.setSelected(true);
        }
    }

    /**
     * Handler for userRadio selectedProperty changes.
     */
    private void userRadioChanged(Object sender) {
        if (ongoingSelection) {
            finishSelection();
        }
        currentFilter.setIsUserCriteria(true);
        if (applyButton.isSelected())
            getContext().setCurrentFilter(currentFilter);
    }

    /**
    * Handler for selectionRadio selectedProperty changes.
    */
    private void selectionRadioChanged(Object sender) {
        currentFilter.setIsUserCriteria(false);
        if (applyButton.isSelected())
            getContext().setCurrentFilter(currentFilter);
    }

    /**
     * Updates the UI to match the currentFilter.
     */
    private void loadCurrentFilterToUi() {
        if (currentFilter.getIsUserCriteria()) {
            searchText.setText(currentFilter.getSearchText());
            userRadio.setSelected(true);
        }
        else {
            selectionRadio.setSelected(true);
        }
        invertFilter.setSelected(currentFilter.getInvert());
        linesBefore.setValue(currentFilter.getBefore());
        linesAfter.setValue(currentFilter.getAfter());
        filterModeBox.setValue(currentFilter.getFilterLayout());
        updateSelectionCount(0);
        switch (currentFilter.getScope()) {
        case AST:
            useAstScope.setSelected(true);
            break;
        case Text:
            useTextScope.setSelected(true);
            break;
        case None:
        default:
            useNone.setSelected(true);
            break;
        }
        currentFilter.addObserver(new Observer() {
            @Override
            public void update(Observable o, Object arg) {
                updateUsedFilter();
            }
        });
    }

    /**
     * Apply a filter or raise a filter change if suppressUsedfilterUpdates is not set.
     */
    private void updateUsedFilter() {
        if (applyButton.isSelected() && !suppressUsedFilterUpdates) {
            getContext().setCurrentFilter(currentFilter);
        }
    }

    /**
     * Completes a selection operation and cleans up the selection UI state (e.g. disables).
     */
    private void finishSelection() {
        if (ongoingSelection) {
            ongoingSelection = false;
            suppressUsedFilterUpdates = false;
            filterSelection.getSelectionModeFinishedEvent()
                    .fire(EmptyEventArgs.get());
            List<String> resolvedSelection = filterSelection
                    .getResolvedSelection();
            currentFilter.setSelections(resolvedSelection);
            updateSelectionCount(resolvedSelection.size());
            filterSelection = null;

            if (selectionFilterToggle.isSelected())
                selectionFilterToggle.setSelected(false);
            applyButton.setDisable(false);
        }
    }

    /*
     * Syncs the range sliders with the corresponding textboxes and labels vice versa.
     */
    private void updateRangeValue(Slider slider, Spinner<Integer> spinner,
            Consumer<Integer> setAction) {
        if (suppressValueUpdate)
            return;

        int nval;
        try {
            nval = Integer.parseInt(spinner.getEditor().getText());
            suppressValueUpdate = true;
            slider.setValue(nval > slider.getMax() ? slider.getMax() : nval);
            suppressValueUpdate = false;
            setAction.accept(nval);
        }
        catch (NumberFormatException e) {
            suppressValueUpdate = true;
            spinner.getEditor().setText("0");
            nval = 0;
            suppressValueUpdate = false;
        }
        setAction.accept(nval);
    }

    /**
     * Updates the "selections" label with the given value.
     */
    private void updateSelectionCount(int value) {
        selectionCount.setText("(selections: " + Integer.toString(value) + ")");
    }

    @Override
    public void setTooltips() {
        invertFilter.setTooltip(new Tooltip(
                "Inverts the filter. Text or selection entered will be unfiltered."));
        useAstScope.setTooltip(
                new Tooltip("Filters based on the abstract syntax tree."));
        useTextScope.setTooltip(new Tooltip(
                "Filters based on the number of lines before and after the filtered text."));
        Tooltip selectionTT = new Tooltip(
                "To filter by selection, click this button first. \n"
                        + "Then make as many selections in the sequent as desired. \n"
                        + "Finally press 'Apply Filter' when done.");
        selectionCount.setTooltip(selectionTT);
        selectionFilterToggle.setTooltip(selectionTT);
        filterModeBox.setTooltip(new Tooltip(
                "Choose whether to minimize or fully collapse the unfiltered text."));
    }
}
