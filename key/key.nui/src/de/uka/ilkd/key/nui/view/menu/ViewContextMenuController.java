package de.uka.ilkd.key.nui.view.menu;

import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewInformation;
import de.uka.ilkd.key.nui.ViewPosition;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.control.CheckMenuItem;

public class ViewContextMenuController extends ViewController {

    private ViewInformation viewInformation;

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

    /**
     * The view this context menu belongs to.
     * 
     * @param view
     */
    public void setParentView(ViewInformation view) {
        viewInformation = view;
    }

    @FXML
    private void handleTopLeft(ActionEvent event) {
        viewInformation.setCurrentPosition(ViewPosition.TOPLEFT);
    }

    @FXML
    private void handleTopRight(ActionEvent event) {
        viewInformation.setCurrentPosition(ViewPosition.TOPRIGHT);
    }

    @FXML
    private void handleBottomLeft(ActionEvent event) {
        viewInformation.setCurrentPosition(ViewPosition.BOTTOMLEFT);
    }

    @FXML
    private void handleBottomRight(ActionEvent event) {
        viewInformation.setCurrentPosition(ViewPosition.BOTTOMRIGHT);
    }

    @FXML
    private void handleCenter(ActionEvent event) {
        viewInformation.setCurrentPosition(ViewPosition.CENTER);
    }

    /**
     * Selects the {@link CheckMenuItem} associated with the current
     * {@link ViewPosition}.
     */
    public void selectPosition() {
        getCheckMenuItem(viewInformation.getCurrentPosition()).setSelected(true);
    }

    /**
     * Returns the {@link CheckMenuItem} associated with a given
     * {@link ViewPosition}.
     * 
     * @param viewPosition
     *            viewPosition
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
