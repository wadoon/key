package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.HashMap;
import java.util.Map;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.Filter;
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

    private Filter currentFilter;

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
    private CheckBox revertFilter;

    private Map<String, Filter> savedFilters = new HashMap<>();

    private void loadCurrentFilter() {
        searchText.setText(currentFilter.getSearchString());
        revertFilter.setSelected(currentFilter.getRevert());
        linesBefore.setValue(currentFilter.getBefore());
        linesAfter.setValue(currentFilter.getAfter());
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

        currentFilter = new Filter();
        loadCurrentFilter();
    }

    @FXML
    private void hanldeRevertChanged() {
        currentFilter.setRevert(revertFilter.isSelected());
        if (revertFilter.isSelected()) {
            linesBefore.setValue(0);
            linesAfter.setValue(0);
        }
        else {
            linesBefore.setValue(2);
            linesAfter.setValue(2);
        }
    }

    @FXML
    private void handleSearchChanged() {
        currentFilter.setSearchString(searchText.getText());
    }

    // TODO: save filter on disk
    // TODO: clear textbox if value changed

    @FXML
    private void handleSaveFilter() {
        String name = filters.getEditor().getText();
        if (name.equals("") || name.equals(null)) {
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
            savedFilters.put(name, currentFilter.Clone());
            filters.getItems().add(currentFilter.getName());
        }
    }

    @FXML
    private void handleFilterSelectionChanged() {
        if (filters.getValue().equals(null))
            return;

        currentFilter = savedFilters.get(filters.getValue());
        loadCurrentFilter();
    }

    @FXML
    private void handleReset() {
        if (savedFilters.containsValue(currentFilter)) {
            // TODO: implement
            // currentfilter needs to be a copy so it can be reset
            filters.getEditor().setText("");
            currentFilter = new Filter();
        }
        else {
            filters.getEditor().setText("");
            currentFilter = new Filter();
        }
        loadCurrentFilter();
    }

    @FXML
    private void handleApply() {
        // XXX not the best approach
        getContext().acceptFilter(currentFilter);
    }
}
