package de.uka.ilkd.key.nui;

import java.util.LinkedList;
import java.util.List;

import javafx.scene.Node;
import javafx.scene.control.TabPane;
import javafx.scene.control.TabPane.TabClosingPolicy;
import javafx.scene.layout.BorderPane;

/**
 * This class represents a view slot at one of the five {@link ViewPosition
 * ViewPositions}.
 * 
 * @author Benedikt Gross
 * @author Victor Schuemmer
 * @author Maximilian Li
 * @version 1.0
 */
public class ViewSlot {
    private List<ViewInformation> tabs = new LinkedList<>();
    private BorderPane uiPane;
    private boolean used = false;
    private boolean pastUsed = false;
    private ViewPosition position;

    /**
     * @return a list containing the {@link ViewInformation ViewInformations}
     *         for all tabs in this slot
     */
    public List<ViewInformation> getTabs() {
        return tabs;
    }

    /**
     * TODO add documentation
     */
    public BorderPane getUiPane() {
        return uiPane;
    }

    /**
     * @return true iff the ViewSlot currently contains any tabs.
     */
    public boolean getUsed() {
        return used;
    }

    /**
     * @return true iff the ViewSlot contained any tabs since last resize
     */
    public boolean getPastUsed() {
        return pastUsed;
    }

    /**
     * The constructor
     * 
     * @param position
     *            the {@link ViewPositon} of the slot
     * @param pane
     */
    public ViewSlot(ViewPosition position, BorderPane pane) {
        this.position = position;
        uiPane = pane;
        currentRegisterer.accept(pane.getCenter());
    }

    /**
     * @return the {@link ViewPositon} of the slot
     */
    public ViewPosition getViewPosition() {
        return position;
    }

    /**
     * Adds the tab in the given {@link ViewInformation} to the slot.
     * 
     * @param view
     *            the ViewInformation containing the tab to add
     */
    public void addTab(ViewInformation view) {
        tabs.add(view);
        view.setIsActive(true);
        TabPane container = ((TabPane) uiPane.getCenter());
        container.getTabs().add(view.getUiTab());
        container.setTabClosingPolicy(TabClosingPolicy.ALL_TABS);
        pastUsed = used;
        used = true;

        container.getSelectionModel().select(view.getUiTab());
    }

    /**
     * Removes the tab in the given {@link ViewInformation} from the slot.
     * 
     * @param view
     *            the ViewInformation containing the tab to remove
     */
    public void removeTab(ViewInformation view) {
        if (!((TabPane) uiPane.getCenter()).getTabs().contains(view.getUiTab()))
            return;
        ((TabPane) uiPane.getCenter()).getTabs().remove(view.getUiTab());
        tabs.remove(view);
        if (tabs.size() == 0) {
            pastUsed = used;
            used = false;
        }
    }

    /**
     * update the pastUsed field of the ViewSlot to the Current used value
     */
    public void updatePastUsed() {
        pastUsed = used;
    }

    private static java.util.function.Consumer<Node> currentRegisterer;

    /**
     * TODO add documentation
     */
    public static void setRegisterDrag(
            java.util.function.Consumer<Node> registerer) {
        currentRegisterer = registerer;
    }
}
