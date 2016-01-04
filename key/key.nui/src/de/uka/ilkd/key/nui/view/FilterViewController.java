package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.ResourceBundle;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.Filter;
import javafx.fxml.FXML;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.TextField;

@KeYView(title = "Filter", path = "FilterView.fxml", preferredPosition = ViewPosition.BOTTOMLEFT)
public class FilterViewController extends ViewController {

    private Filter currentFilter;

    @FXML
    private TextField searchText;

    @FXML
    private TextField excludeText;

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

    private Document dummyDoc;

    @FXML
    private void handleApply() {
        fillCurrentFilter();
        NodeList nodeList = dummyDoc.getElementsByTagName("*");
        List<Node> excludes = new LinkedList<>();
        List<Node> includes = new LinkedList<>();

        for (int i = 0; i < nodeList.getLength(); i++) {
            Node node = nodeList.item(i);
            if (node.getNodeType() == Node.ELEMENT_NODE) {
                if (currentFilter.getSearchString() != null
                        && !currentFilter.getSearchString().equals("")
                        && !node.getTextContent()
                                .contains(currentFilter.getSearchString()))
                    includes.add(node);
                else if (currentFilter.getExcludeString() != null
                        && !currentFilter.getExcludeString().equals("")
                        && node.getTextContent()
                                .contains(currentFilter.getExcludeString()))
                    excludes.add(node);
            }
        }
        String filterStyles = "";
        filterStyles += applyInclude(includes);
        filterStyles += applyExclude(excludes);
        Element element = dummyDoc.getElementById("filterCss");
        if (element != null)
            element.setTextContent(filterStyles);
        else {
            element = dummyDoc.createElement("style");
            element.setIdAttribute("filterCss", true);
            element.setTextContent(filterStyles);
        }
        /*
         * for (Node node : dummy.getChildren()) { if (node instanceof Text) {
         * Text text = (Text) node; if (currentFilter.getSearchString() != null
         * && !currentFilter.getSearchString().equals("") &&
         * !text.getText().contains(currentFilter.getSearchString()))
         * text.setVisible(false); else if(currentFilter.getExcludeString() !=
         * null && !currentFilter.getExcludeString().equals("") &&
         * text.getText().contains(currentFilter.getExcludeString()))
         * text.setVisible(false); else text.setVisible(true); } }
         */
    }

    private String applyInclude(List<Node> applyTo) {
        return addFilter(
                ".content :not(%s),.content :not(%s) *{display: none !important;}",
                applyTo);
    }

    private String applyExclude(List<Node> applyTo) {
        return addFilter(
                ".content (%s),.content (%s) *{display: none !important;}",
                applyTo);
    }

    private String addFilter(String css, List<Node> applyTo) {
        List<String> classes = new LinkedList<>();
        for (Node node : applyTo)
            classes.add(node.getAttributes().getNamedItem("class")
                    .getTextContent());
        String htmlClasses = String.join(",", classes);
        if (applyTo.size() > 0)
            return String.format(css, htmlClasses, htmlClasses);
        else
            return "";
    }

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
        excludeText.setText(currentFilter.getExcludeString());
        toggleUseTerm.setSelected(currentFilter.getUseTerm());
    }

    private void fillCurrentFilter() {
        currentFilter.setSearchString(searchText.getText());
        currentFilter.setExcludeString(excludeText.getText());
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
    }

    @Override
    public void initializeAfterLoadingFxml() {
        // TODO Auto-generated method stub
    }
}
