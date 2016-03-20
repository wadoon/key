package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.List;
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
import javafx.fxml.FXML;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.RadioButton;
import javafx.scene.control.Slider;
import javafx.scene.control.Spinner;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.layout.GridPane;

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
    private Button applyButton;

    @FXML
    private RadioButton useAstScope;

    @FXML
    private RadioButton useTextScope;

    @FXML
    private RadioButton useNone;

    @FXML
    private GridPane resultRangeText;

    private FilterSelection filterSelection;
    private boolean suppressValueUpdate = false;

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
        // TODO implement all this as handling functions

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
        filterModeBox.valueProperty().addListener((o, old_val,
                new_val) -> currentFilter.setFilterLayout(new_val));

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

    private void updateRangeValue(Slider slider, Spinner<Integer> spinner,
            Consumer<Integer> setAction) {
        if (suppressValueUpdate)
            return;

        int nval;
        try {
            nval = Integer.parseInt(spinner.getEditor().getText());
            if (nval > slider.getMax()) {
                suppressValueUpdate = true;
                slider.setValue(slider.getMax());
                suppressValueUpdate = false;
            }
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
}
