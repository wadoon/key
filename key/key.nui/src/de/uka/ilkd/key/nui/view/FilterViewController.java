package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.security.spec.ECPrivateKeySpec;
import java.util.HashMap;
import java.util.Map;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.Filter;
import javafx.fxml.FXML;
import javafx.scene.Node;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.TextField;
import javafx.scene.text.Text;
import javafx.scene.text.TextFlow;

@KeYView(title = "Filter", path = "FilterView.fxml", preferredPosition = ViewPosition.BOTTOMLEFT)
public class FilterViewController extends ViewController {

    private Filter currentFilter;

    @FXML
    private TextField searchText;

    @FXML
    private CheckBox toggleUseTerm;

    @FXML
    private ComboBox<String> filters;

    @FXML
    private void handleReset() {
        filters.getEditor().setText("");
        currentFilter = new Filter();
        loadCurrentFilter();
    }

    @FXML
    private void handleApply() {
        fillCurrentFilter();
        for (Node node : dummy.getChildren()) {
            if (node instanceof Text) {
                Text text = (Text) node;
                if (currentFilter.getSearchString() != null
                        && !currentFilter.getSearchString().equals("")
                        && text.getText().contains(currentFilter.getSearchString()))
                    text.setVisible(false);
                else text.setVisible(true);
            }
        }
    }

    @FXML
    private TextFlow dummy;

    // TODO: save filter on disk
    // TODO: clear textbox if value changed

    @FXML
    private void handleSaveFilter() {
        String name = filters.getEditor().getText();
        if (name.equals("") || name.equals(null))
            return;

        if (savedFilters.containsKey(name)) {
            currentFilter = savedFilters.get(name);
            fillCurrentFilter();
        }
        else {
            fillCurrentFilter();
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

    private Map<String, Filter> savedFilters = new HashMap<>();

    private void loadCurrentFilter() {
        searchText.setText(currentFilter.getSearchString());
        toggleUseTerm.setSelected(currentFilter.getUseTerm());
    }

    private void fillCurrentFilter() {
        currentFilter.setSearchString(searchText.getText());
        currentFilter.setUseTerm(toggleUseTerm.isSelected());
    }

    /*
     * private void doFilter(String filterstring) { if (!sequentLoaded) return;
     * if (filterstring.startsWith(".")) printer.addTempCss("filterCss",
     * String.format(
     * ".content :not(%s),.content :not(%s) *{display: none !important;}",
     * filterstring, filterstring)); else printer.addTempCss("filterCss", "");
     * updateHtml(printer.printSequent(proofString)); }
     */

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        currentFilter = new Filter();
        dummy.getChildren().add(new Text(" \\forall "));
        dummy.getChildren().add(new Text(" forall "));
        dummy.getChildren().add(new Text("<>"));
        dummy.getChildren().add(new Text(" and "));
        dummy.getChildren().add(new Text(" or "));
    }

    @Override
    public void initializeAfterLoadingFxml() {
        // TODO Auto-generated method stub
    }
}
