/**
 * 
 */
package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.view.menu.TacletMenuItem;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.ProgramPrinter;
import javafx.event.Event;
import javafx.fxml.FXML;
import javafx.scene.control.ListView;
import javafx.scene.control.TextArea;

/**
 * @author Victor Schuemmer
 *
 */
public class InsertionBrowserViewController extends ViewController {

    @FXML
    private ListView<TacletMenuItem> itemList;
    @FXML
    private TextArea preview;

    @Override
    public void initialize(URL arg0, ResourceBundle arg1) {
        itemList.getSelectionModel().selectedItemProperty().addListener((val, oldVal, newVal) -> {
            preview.setText(getDescription(newVal));
        });     
    }
    
    @Override
    public void initializeAfterLoadingFxml() {
        itemList.getItems().addAll(getContext().getCurrentHiddenTacletMenuItems());
        itemList.getSelectionModel().select(0);
    }
    
    @FXML
    private void handleApply(Event event) {
        TacletMenuItem item = itemList.getSelectionModel().getSelectedItem();
        item.performAction();
        handleClose(event);
    }

    @FXML
    private void handleClose(Event event) {
        getStage().close();
    }

    private String getDescription(TacletMenuItem item) {
        final LogicPrinter printer = new LogicPrinter(new ProgramPrinter(),
                item.getNotationInfo(), item.getServices(), true);
        printer.setInstantiation(item.getTacletApp().instantiations());
        printer.printSequent(item.getTaclet().goalTemplates().head().sequent());
        return printer.toString();
    }
}
