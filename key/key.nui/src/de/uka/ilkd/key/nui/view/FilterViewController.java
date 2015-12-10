package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.Filter;
import javafx.fxml.FXML;
import javafx.scene.control.CheckBox;
import javafx.scene.control.TextField;

@KeYView(title="Filter",path="FilterView.fxml",preferredPosition=ViewPosition.TOPRIGHT)
public class FilterViewController extends ViewController {

    private Filter currentFilter;
    
    @FXML
    private TextField searchText;
    
    @FXML
    private CheckBox toggleUseTerm;
    
    @FXML
    private void handleReset(){
        currentFilter.reset();
        loadFilter();
    }
    
    @FXML
    private void handleApply(){
        currentFilter.setSearchString(searchText.getText());
        currentFilter.setUseTerm(toggleUseTerm.isSelected());
    }
    
    private void loadFilter(){
        searchText.setText(currentFilter.getSearchString());
        toggleUseTerm.setSelected(currentFilter.getUseTerm());
    }
    /*
    private void doFilter(String filterstring) {
        if (!sequentLoaded)
            return;
        if (filterstring.startsWith("."))
            printer.addTempCss("filterCss", String.format(
                    ".content :not(%s),.content :not(%s) *{display: none !important;}", filterstring, filterstring));
        else
            printer.addTempCss("filterCss", "");
        updateHtml(printer.printSequent(proofString));
    }*/

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        currentFilter = new Filter();
    }

    @Override
    public void initializeAfterLoadingFxml() {
        // TODO Auto-generated method stub
        
    }
}
