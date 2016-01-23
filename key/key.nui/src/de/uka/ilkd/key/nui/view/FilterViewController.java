package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.HashMap;
import java.util.Map;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.PrintFilter;
import de.uka.ilkd.key.nui.model.PrintFilter.FilterMode;
import javafx.fxml.FXML;
import javafx.scene.control.Alert;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;
import javafx.scene.control.Slider;
import javafx.scene.control.TextField;
import javafx.scene.control.Alert.AlertType;

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
    private ComboBox<FilterMode> filterModeBox;

    private Map<String, PrintFilter> savedFilters = new HashMap<>();

    private void loadCurrentFilter() {
        searchText.setText(currentFilter.getSearchString());
        invertFilter.setSelected(currentFilter.getInvert());
        linesBefore.setValue(currentFilter.getBefore());
        linesAfter.setValue(currentFilter.getAfter());
        filterModeBox.setValue(currentFilter.getFilterMode());
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        linesBefore.valueProperty().addListener((o, old_val, new_val) -> {
            beforeNumber.setText(Integer.toString(new_val.intValue()));
            currentFilter.setBefore(new_val.intValue());
        });
        linesAfter.valueProperty().addListener((o, old_val, new_val) -> {
            afterNumber.setText(Integer.toString(new_val.intValue()));
            currentFilter.setAfter(new_val.intValue());
        });
        searchText.textProperty().addListener((o, old_val,
                new_val) -> currentFilter.setSearchString(new_val));
        filterModeBox.valueProperty().addListener(
                (o, old_val, new_val) -> currentFilter.setFilterMode(new_val));
        filterModeBox.getItems().add(FilterMode.Minimize);
        filterModeBox.getItems().add(FilterMode.Collapse);
        
        currentFilter = new PrintFilter();
        loadCurrentFilter();
    }

    @FXML
    private void hanldeInvertChanged() {
        currentFilter.setInvert(invertFilter.isSelected());
        if (invertFilter.isSelected()) {
            linesBefore.setValue(0);
            linesAfter.setValue(0);
        }
        else {
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
        // XXX not the best approach
        getContext().acceptFilter(currentFilter);
    }
}
