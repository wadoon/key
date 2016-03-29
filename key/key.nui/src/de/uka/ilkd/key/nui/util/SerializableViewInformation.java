package de.uka.ilkd.key.nui.util;

import java.security.InvalidParameterException;

import de.uka.ilkd.key.nui.ViewInformation;
import de.uka.ilkd.key.nui.ViewPosition;

/**
 * Stores all information needed to save or restore a {@link ViewInformation} in
 * value types.
 * 
 * @author Benedikt Gross
 * @version 1.0
 */
public class SerializableViewInformation {

    private String fxmlUrl;

    /**
     * Returns the url to the fxml used for this object.
     * 
     * @return
     */
    public String getFxmlUrl() {
        return fxmlUrl;
    }

    private boolean isactive;

    /**
     * Returns true if the view was active the last time.
     */
    public boolean getIsActibe() {
        return isactive;
    }

    private ViewPosition viewPosition;

    /**
     * Returns the {@link ViewPosition} the view was in the last time.
     */
    public ViewPosition getViewPosition() {
        return viewPosition;
    }

    /**
     * Creates a serializable version of the passed {@link ViewInformation}.
     * 
     * @param view
     *            The {@link ViewInformation} that is to be serialized.
     */
    public SerializableViewInformation(ViewInformation view) {
        viewPosition = view.getCurrentPosition();
        isactive = view.getIsActive();
        fxmlUrl = view.getFxmlPath().getPath();
    }

    /**
     * Returns a string representation of this object. The values are separated
     * by commas.
     */
    public String getSerialized() {
        return fxmlUrl + "," + viewPosition.toString() + "," + isactive;
    }

    /**
     * Recreates a {@link SerializableViewInformation} from its string
     * representation.
     */
    public SerializableViewInformation(String data) {
        String[] dataArr = data.split(",");
        if (dataArr.length != 3)
            throw new InvalidParameterException("data was invalid");
        fxmlUrl = dataArr[0];
        viewPosition = Enum.valueOf(ViewPosition.class, dataArr[1]);
        isactive = Boolean.parseBoolean(dataArr[2]);
    }
}
