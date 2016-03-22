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
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.VBox;

@KeYView(title = "Filter", path = "FilterView.fxml", preferredPosition = ViewPosition.BOTTOMLEFT, defaultActive = false)
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
    private GridPane resultRangeText;

    @FXML
    private Label selectionCount;

    @FXML
    private AnchorPane filterContainer;
    
    @FXML
    private VBox filterSettings;

    private FilterSelection filterSelection;
    private boolean suppressValueUpdate = false;
    private boolean suppressUsedFilterUpdates = false;

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        selectionFilterToggle.setStyle(
                "-fx-background-image: url('" + NUIConstants.FILTER_MOUSE_ICON
                        + "');" + "-fx-background-position: center center;"
                        + "-fx-background-repeat: no-repeat;"
                        + "-fx-background-size: contain;");
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
        applyButton.selectedProperty().addListener(event -> handleApply());

        // default data
        filterModeBox.getItems().add(FilterLayout.Minimize);
        filterModeBox.getItems().add(FilterLayout.Collapse);
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
                        applyButton.setDisable(!getContext().getKeYMediator()
                                .ensureProofLoaded());
                        filterSettings.setDisable(!getContext().getKeYMediator()
                                .ensureProofLoaded());
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
    private void handleApply() {
        if (applyButton.isSelected()) {
            if (filterSelection != null) {
                selectionFilterToggle.setSelected(false);
                finishSelection();
            }
            getContext().setCurrentFilter(currentFilter);
        }
        else {
            getContext().setCurrentFilter(null);
            updateSelectionCount(0);
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
            currentFilter.setIsUserCriteria(false);
            getContext().activateSelectMode(filterSelection);
        }
        else {
            applyButton.setDisable(false);
            suppressUsedFilterUpdates = false;
            finishSelection();
            updateUsedFilter();
        }
    }

    private void userRadioChanged(Object sender) {
        if (filterSelection != null) {
            selectionFilterToggle.setSelected(false);
            finishSelection();
        }
        updateSelectionCount(0);
        currentFilter.setIsUserCriteria(true);
        if (applyButton.isSelected())
            getContext().setCurrentFilter(currentFilter);
    }

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

    private void updateUsedFilter() {
        if (applyButton.isSelected() && !suppressUsedFilterUpdates) {
            getContext().setCurrentFilter(currentFilter);
        }
    }

    private void finishSelection() {
        filterSelection.getSelectionModeFinishedEvent()
                .fire(EmptyEventArgs.get());
        List<String> resolvedSelection = filterSelection.getResolvedSelection();
        currentFilter.setSelections(resolvedSelection);
        filterSelection = null;
        updateSelectionCount(resolvedSelection.size());
    }

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

    private void updateSelectionCount(int value) {
        selectionCount.setText("(selections: " + Integer.toString(value) + ")");
    }
    
    @Override
    public void setTooltips() {
        invertFilter.setTooltip(new Tooltip("Inverts the filter. Text or selection entered will be unfiltered."));
        useAstScope.setTooltip(new Tooltip("Filters based on the abstract syntax tree."));
        useTextScope.setTooltip(new Tooltip("Filters based on the number of lines before and after the filtered text."));
        Tooltip selectionTT = new Tooltip("To filter by selection, click this button first. \n"
                + "Then make as many selections in the sequent as desired. \n"
                + "Finally press 'Apply Filter' when done.");
        selectionCount.setTooltip(selectionTT);
        selectionFilterToggle.setTooltip(selectionTT);
        filterModeBox.setTooltip(new Tooltip("Choose whether to minimize or fully collapse the unfiltered text."));
    }
}
