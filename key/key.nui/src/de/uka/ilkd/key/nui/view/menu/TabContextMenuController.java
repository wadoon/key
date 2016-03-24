package de.uka.ilkd.key.nui.view.menu;

import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewInformation;
import de.uka.ilkd.key.nui.ViewPosition;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.control.CheckMenuItem;

/**
 * Context menu for any {@link ViewInformation view} open in a tab.
 * 
 * @author Benedikt Gross
 * @author Nils Muzzulini
 * @version 1.0
 */
public class TabContextMenuController extends ViewController {

    @FXML
    CheckMenuItem topLeft;
    @FXML
    CheckMenuItem topRight;
    @FXML
    CheckMenuItem bottomLeft;
    @FXML
    CheckMenuItem bottomRight;
    @FXML
    CheckMenuItem center;

    private ViewInformation view;

    /**
     * The {@link ViewInformation view} this context menu belongs to.
     * 
     * @param view
     */
    public void setParentView(ViewInformation view) {
        this.view = view;
    }

    @FXML
    private void handleTopLeft(ActionEvent event) {
        view.setCurrentPosition(ViewPosition.TOPLEFT);
    }

    @FXML
    private void handleTopRight(ActionEvent event) {
        view.setCurrentPosition(ViewPosition.TOPRIGHT);
    }

    @FXML
    private void handleBottomLeft(ActionEvent event) {
        view.setCurrentPosition(ViewPosition.BOTTOMLEFT);
    }

    @FXML
    private void handleBottomRight(ActionEvent event) {
        view.setCurrentPosition(ViewPosition.BOTTOMRIGHT);
    }

    @FXML
    private void handleCenter(ActionEvent event) {
        view.setCurrentPosition(ViewPosition.CENTER);
    }

    /**
     * Selects the {@link CheckMenuItem} associated with the current
     * {@link ViewPosition}.
     */
    public void selectPosition() {
        getCheckMenuItem(view.getCurrentPosition()).setSelected(true);
    }

    /**
     * Returns the {@link CheckMenuItem} associated with a given
     * {@link ViewPosition}.
     * 
     * @param viewPosition
     * @return checkMenuItem
     */
    private CheckMenuItem getCheckMenuItem(ViewPosition viewPosition) {
        switch (viewPosition) {
        case TOPLEFT:
            return topLeft;
        case TOPRIGHT:
            return topRight;
        case BOTTOMRIGHT:
            return bottomRight;
        case BOTTOMLEFT:
            return bottomLeft;
        case CENTER:
            return center;
        default:
            return null;
        }
    }
}
