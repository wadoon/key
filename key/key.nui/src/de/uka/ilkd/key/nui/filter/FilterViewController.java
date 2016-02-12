package de.uka.ilkd.key.nui.filter;

import java.net.URL;
import java.util.HashMap;
import java.util.Map;
import java.util.ResourceBundle;
import java.util.function.Consumer;

import com.google.common.util.concurrent.Service.Listener;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.filter.PrintFilter.FilterLayout;
import de.uka.ilkd.key.util.Pair;
import javafx.fxml.FXML;
import javafx.scene.control.Alert;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;
import javafx.scene.control.RadioButton;
import javafx.scene.control.Slider;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.Button;
import javafx.scene.layout.BorderPane;
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
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        searchText.disableProperty().bind(selectionRadio.selectedProperty());
        selectionFilterToggle.disableProperty()
                .bind(userRadio.selectedProperty());
        applyButton.setDisable(true);

        linesBefore.valueProperty().addListener((o, old_val, new_val) -> {
            beforeNumber.setText(Integer.toString(new_val.intValue()));
            currentFilter.setBefore(new_val.intValue());
        });
        linesAfter.valueProperty().addListener((o, old_val, new_val) -> {
            afterNumber.setText(Integer.toString(new_val.intValue()));
            currentFilter.setAfter(new_val.intValue());
        });
        searchText.textProperty()
                .addListener((o, old_val, new_val) -> currentFilter.setSearchText(new_val));
        filterModeBox.valueProperty().addListener((o, old_val,
                new_val) -> currentFilter.setFilterLayout(new_val));
        filterModeBox.getItems().add(FilterLayout.Minimize);
        filterModeBox.getItems().add(FilterLayout.Collapse);

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
        currentFilter = new PrintFilter();
        loadCurrentFilter();
        handleApply();
    }

    @FXML
    private void handleApply() {
        if (filterSelection != null) {
            selectionFilterToggle.setSelected(false);
            finishSelection();
        }
        getContext().setCurrentPrintFilter(currentFilter);
    }

    private FilterSelection filterSelection;

    @FXML
    private void handleSelectionFilterToggled() {
        if (selectionFilterToggle.isSelected()) {
            // reset old filter to make selection more easily
            getContext().setCurrentPrintFilter(new PrintFilter());
            filterSelection = new FilterSelection();
            currentFilter.setIsUserCriteria(false);
            getContext().activateSelectMode(filterSelection);
        }
        else {
            finishSelection();
            getContext().setCurrentPrintFilter(currentFilter);
        }
    }

    private void finishSelection() {
        filterSelection.getSelectionModeFinishedEvent()
                .fire(EmptyEventArgs.get());
        currentFilter.setSelectionCriteria(filterSelection.getCriteria());
        filterSelection = null;
    }
}
