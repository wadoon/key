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

/**
 * A menu for TacletMenuItems whose taclets insert hidden terms.
 * 
 * @author Victor Schuemmer
 */
public class InsertHiddenMenuController extends ViewController {

    @FXML
    private Menu rootMenu;
    private ObservableList<TacletMenuItem> itemList;

    @Override
    public void initialize(URL arg0, ResourceBundle arg1) {
        this.itemList = FXCollections.observableArrayList();
    }

    /**
     * Checks if this menu is responsible for the item (if the item is for
     * inserting a hidden term).
     * 
     * @param item
     *            the TacletMenuItem to check
     * @return true iff the menu is responsible for the item and the item can be
     *         added without the risk of producing errors when opening the
     *         insertion dialog.
     */
    public boolean isResponsible(TacletMenuItem item) {
        if (!(item.getTaclet() instanceof NoFindTaclet)
                || !item.getTaclet().displayName().startsWith("insert_hidden"))
            return false;
        final ImmutableList<TacletGoalTemplate> goalTemplates = item.getTaclet()
                .goalTemplates();
        return (goalTemplates.size() == 1);

    }

    /**
     * Adds a new item to this menu. Assumes that the item is applicable (you
     * can check with isResponsible()). Adding items that this menu is not
     * responsible for may produce errors when opening the insertion dialog.
     * 
     * @param item
     *            the TacletMenuItem to add
     */
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

    /**
     * @return true iff the number of items added is zero.
     */
    public boolean isEmpty() {
        return itemCount() == 0;
    }

    /**
     * @return the number of items in this menu, excluding the 'Open Dialog'
     *         item.
     */
    public int itemCount() {
        return itemList.size();
    }

    /**
     * Sets the visibility of this menu.
     * 
     * @param visible
     *            true to make the menu visible, false to make it invisible
     */
    public void setVisible(boolean visible) {
        rootMenu.setVisible(visible);
    }

    /**
     * Action for the menu item 'Open Dialog'. Opens a window for selection of a
     * hidden element to insert.
     * 
     * @param event
     */
    @FXML
    private void handleOpenDialog(Event event) {
        getContext().setCurrentHiddenTacletMenuItems(itemList);
        getMainApp().openNewWindow("Insertion Browser",
                "view/InsertionBrowser.fxml", false, false);
    }
}
