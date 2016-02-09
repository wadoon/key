package de.uka.ilkd.key.nui.filter;

import java.net.URL;
import java.util.HashMap;
import java.util.Map;
import java.util.ResourceBundle;
import java.util.function.Consumer;

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
import javafx.scene.control.Slider;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.GridPane;

@KeYView(title = "Filter", path = "FilterView.fxml", preferredPosition = ViewPosition.BOTTOMLEFT)
public class FilterViewController extends ViewController {

    private PrintFilter currentFilter;

    @FXML
    private TextField searchText;

    @FXML
    private ComboBox<String> filters;

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
    private GridPane userCriteria;

    @FXML
    private BorderPane selectionCriteria;

    @FXML
    private ToggleButton selectionFilterToggle;

    private Map<String, PrintFilter> savedFilters = new HashMap<>();
    private String searchValue;
    private boolean invert;

    private void loadCurrentFilter() {
        if (currentFilter.getIsUserCriteria()) {
            Criteria<?> criteria = currentFilter.getCriteria();
            if (criteria instanceof NotCriteria<?>) {
                invert = true;
                searchText.setText(
                        ((CriterionContainsString) ((NotCriteria<?>) criteria)
                                .getChildCriteria()).getSearchString());
            }
            else {
                invert = false;
                if (criteria instanceof CriterionContainsString) {
                    searchText.setText(((CriterionContainsString) criteria)
                            .getSearchString());
                }
                else {
                    // this happens if upgraded from version without criteria
                    searchText.setText("");
                }
            }

            invertFilter.setSelected(invert);
            toggleIsUserCriteria(true);
        }
        else {
            toggleIsUserCriteria(false);
        }

        linesBefore.setValue(currentFilter.getBefore());
        linesAfter.setValue(currentFilter.getAfter());
        filterModeBox.setValue(currentFilter.getFilterLayout());
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        // bind to hide if visiblity is changed
        selectionCriteria.managedProperty()
                .bind(selectionCriteria.visibleProperty());
        userCriteria.managedProperty().bind(userCriteria.visibleProperty());

        linesBefore.valueProperty().addListener((o, old_val, new_val) -> {
            beforeNumber.setText(Integer.toString(new_val.intValue()));
            currentFilter.setBefore(new_val.intValue());
        });
        linesAfter.valueProperty().addListener((o, old_val, new_val) -> {
            afterNumber.setText(Integer.toString(new_val.intValue()));
            currentFilter.setAfter(new_val.intValue());
        });
        searchText.textProperty()
                .addListener((o, old_val, new_val) -> searchValue = new_val);
        filterModeBox.valueProperty().addListener((o, old_val,
                new_val) -> currentFilter.setFilterLayout(new_val));
        filterModeBox.getItems().add(FilterLayout.Minimize);
        filterModeBox.getItems().add(FilterLayout.Collapse);

        currentFilter = new PrintFilter();
        loadCurrentFilter();
    }

    @FXML
    private void hanldeInvertChanged() {
        if (invertFilter.isSelected()) {
            invert = true;
            linesBefore.setValue(0);
            linesAfter.setValue(0);
        }
        else {
            invert = false;
            linesBefore.setValue(2);
            linesAfter.setValue(2);
        }
    }

    // TODO: save filter on disk

    @FXML
    private void handleSaveFilter() {
        String name = filters.getEditor().getText();
        if (name.isEmpty()) {
            Alert alert = new Alert(AlertType.WARNING);
            alert.setContentText("Please choose a name before saving!");
            alert.showAndWait();
            return;
        }
        if (currentFilter.getIsUserCriteria()) {
            if (invert)
                currentFilter.setCriteria(new NotCriteria<>(
                        new CriterionContainsString(searchValue)));
            else
                currentFilter
                        .setCriteria(new CriterionContainsString(searchValue));
        }

        if (savedFilters.containsKey(name)) {
            currentFilter = savedFilters.get(name);
        }
        else {
            currentFilter.setName(name);
            savedFilters.put(name, currentFilter.cloneFilter());
            filters.getItems().add(currentFilter.getName());
        }
    }

    @FXML
    private void handleFilterSelectionChanged() {
        if (filters.getValue() == null)
            return;

        currentFilter = savedFilters.get(filters.getValue());
        loadCurrentFilter();
    }

    @FXML
    private void handleReset() {
        filters.getEditor().setText("");
        currentFilter = new PrintFilter();
        loadCurrentFilter();
        handleApply();
    }

    @FXML
    private void handleApply() {
        getContext().setCurrentPrintFilter(currentFilter);
    }

    @FXML
    private void handleSelectionFilterToggled() {
        if (selectionFilterToggle.isSelected()) {
            currentFilter.setIsUserCriteria(false);
            getContext().activateSelectMode(this::selectionModeCallback);
        }
        else {
            currentFilter.setIsUserCriteria(true);
            // TODO: add cancel event to event args
        }
    }

    private void toggleIsUserCriteria(boolean value) {
        userCriteria.setVisible(value);
        selectionCriteria.setVisible(!value);
    }

    private void selectionModeCallback(
            Criteria<Pair<Integer, String>> criteria) {
        currentFilter.setCriteria(criteria);
    }
}
