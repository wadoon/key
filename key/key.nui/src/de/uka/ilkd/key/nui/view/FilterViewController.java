package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.ResourceBundle;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.event.EmptyEventArgs;
import de.uka.ilkd.key.nui.filter.FilterSelection;
import de.uka.ilkd.key.nui.filter.PrintFilter;
import de.uka.ilkd.key.nui.filter.PrintFilter.FilterLayout;
import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import javafx.fxml.FXML;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;
import javafx.scene.control.RadioButton;
import javafx.scene.control.Slider;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.layout.GridPane;

@KeYView(title = "Filter", path = "FilterView.fxml", preferredPosition = ViewPosition.BOTTOMLEFT)
public class FilterViewController extends ViewController {

    private PrintFilter currentFilter;

    @FXML
    private TextField searchText;

    // @FXML
    // private ComboBox<String> filters;

    @FXML
    private Slider linesBefore;

    @FXML
    private Label beforeNumber;

    @FXML
    private Slider linesAfter;

    @FXML
    private Label afterNumber;

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
    private Button applyButton;

    @FXML
    private RadioButton useAstScope;

    @FXML
    private RadioButton useTextScope;

    @FXML
    private GridPane resultRangeText;

    // Note: used in code that is disabled right now.
    @SuppressFBWarnings(justification = "Not used in code right now", value = "URF_UNREAD_FIELD")

    private Map<String, PrintFilter> savedFilters = new HashMap<>();

    private void loadCurrentFilter() {
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
        useAstScope.setSelected(currentFilter.getUseAstScope());
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        // ui bindings
        searchText.disableProperty().bind(userRadio.selectedProperty().not());
        selectionFilterToggle.disableProperty()
                .bind(selectionRadio.selectedProperty().not());
        resultRangeText.disableProperty()
                .bind(useTextScope.selectedProperty().not());
        invertFilter.disableProperty()
                .bind(useAstScope.selectedProperty().not());

        // change propagation to currentFilter
        //TODO implement all this as handling functions
        linesBefore.valueProperty().addListener((o, old_val, new_val) -> {
            beforeNumber.setText(Integer.toString(new_val.intValue()));
            currentFilter.setBefore(new_val.intValue());
        });
        linesAfter.valueProperty().addListener((o, old_val, new_val) -> {
            afterNumber.setText(Integer.toString(new_val.intValue()));
            currentFilter.setAfter(new_val.intValue());
        });
        searchText.textProperty().addListener(
                (o, old_val, new_val) -> currentFilter.setSearchText(new_val));
        filterModeBox.valueProperty().addListener((o, old_val,
                new_val) -> currentFilter.setFilterLayout(new_val));
        useAstScope.selectedProperty().addListener(
                (o, old_val, new_val) -> currentFilter.setUseAstScope(new_val));
        userRadio.selectedProperty().addListener(event -> {
            if (filterSelection != null) {
                selectionFilterToggle.setSelected(false);
                finishSelection();
            }
            currentFilter.setIsUserCriteria(true);
        });

        // default data
        filterModeBox.getItems().add(FilterLayout.Minimize);
        filterModeBox.getItems().add(FilterLayout.Collapse);
        applyButton.setDisable(true);
        useTextScope.setSelected(true);
        
        currentFilter = new PrintFilter();
        loadCurrentFilter();
    }

    @Override
    public void initializeAfterLoadingFxml() {
        getContext().getKeYMediator()
                .addKeYSelectionListener(new KeYSelectionListener() {
                    @Override
                    public void selectedProofChanged(KeYSelectionEvent e) {
                        if (getContext().getKeYMediator()
                                .getSelectedProof() != null)
                            applyButton.setDisable(false);
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

    // TODO: save filter on disk

    @FXML
    private void handleSaveFilter() {
        /*
         * String name = filters.getEditor().getText(); if (name.isEmpty()) {
         * Alert alert = new Alert(AlertType.WARNING); alert.setContentText(
         * "Please choose a name before saving!"); alert.showAndWait(); return;
         * } updateCurrentFilter();
         * 
         * if (savedFilters.containsKey(name)) { currentFilter =
         * savedFilters.get(name); } else { currentFilter.setName(name);
         * savedFilters.put(name, currentFilter.cloneFilter());
         * filters.getItems().add(currentFilter.getName()); }
         */
    }

    @FXML
    private void handleFilterSelectionChanged() {
        /*
         * if (filters.getValue() == null) return;
         * 
         * currentFilter = savedFilters.get(filters.getValue());
         * loadCurrentFilter();
         */
    }

    @FXML
    private void handleReset() {
        getContext().setCurrentFilter(null);
    }

    @FXML
    private void handleApply() {
        if (filterSelection != null) {
            selectionFilterToggle.setSelected(false);
            finishSelection();
        }
        getContext().setCurrentFilter(currentFilter);
    }

    private FilterSelection filterSelection;

    @FXML
    private void handleSelectionFilterToggled() {
        if (selectionFilterToggle.isSelected()) {
            // reset old filter to make selection more easily
            getContext().setCurrentFilter(null);
            filterSelection = new FilterSelection();
            currentFilter.setIsUserCriteria(false);
            getContext().activateSelectMode(filterSelection);
            selectionFilterToggle.setStyle("-fx-background-color: #ff6666;");
        }
        else {
            finishSelection();
            getContext().setCurrentFilter(currentFilter);
        }
    }

    private void finishSelection() {
        filterSelection.getSelectionModeFinishedEvent()
                .fire(EmptyEventArgs.get());
        List<String> resolvedSelection = filterSelection.getResolvedSelection();
        currentFilter.setSelections(resolvedSelection);
        filterSelection = null;

        selectionFilterToggle.setStyle("-fx-background-color: lightgrey;");
    }
}
