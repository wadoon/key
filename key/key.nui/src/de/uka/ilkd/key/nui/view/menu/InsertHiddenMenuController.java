package de.uka.ilkd.key.nui.view.menu;

import java.net.URL;
import java.util.ResourceBundle;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.event.Event;
import javafx.fxml.FXML;
import javafx.scene.control.Menu;

public class InsertHiddenMenuController extends ViewController {

    @FXML
    private Menu rootMenu;
    private ObservableList<TacletMenuItem> itemList;

    @Override
    public void initialize(URL arg0, ResourceBundle arg1) {
        this.itemList = FXCollections.observableArrayList();
    }

    public boolean isResponsible(TacletMenuItem item) {
        if (!(item.getTaclet() instanceof NoFindTaclet)
                || !item.getTaclet().displayName().startsWith("insert_hidden"))
            return false;
        final ImmutableList<TacletGoalTemplate> goalTemplates = item.getTaclet()
                .goalTemplates();
        return (goalTemplates.size() == 1);

    }

    public void add(TacletMenuItem item) {
        ImmutableList<TacletGoalTemplate> templates = item.getTaclet()
                .goalTemplates();
        if (templates.size() == 1) {
            final LogicPrinter printer = new LogicPrinter(new ProgramPrinter(),
                    new NotationInfo(),
                    getContext().getKeYMediator().getServices(), true);
            printer.setInstantiation(item.getTacletApp().instantiations());
            printer.printSequent(templates.head().sequent());
            String s = printer.toString();
            if (s.length() > 40) {
                s = s.substring(0, 37) + "...";
            }
            item.setText(s);
        }

        rootMenu.getItems().add(item);
        itemList.add(item);
        rootMenu.setText("Insert Hidden (" + itemCount()
                + (itemCount() != 1 ? " items" : " item") + ")");
    }

    public boolean isEmpty() {
        return itemCount() == 0;
    }

    public int itemCount() {
        // Not counting open dialog
        return itemList.size();
    }

    public void setVisible(boolean visible) {
        rootMenu.setVisible(visible);
    }
    
    @FXML
    private void handleOpenDialog(Event event) {
        getContext().setCurrentHiddenTacletMenuItems(itemList);
        getMainApp().openNewWindow("Insertion Browser",
                "view/InsertionBrowser.fxml", false);    
    }
}
