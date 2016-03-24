package de.uka.ilkd.key.nui.util;

import java.security.InvalidParameterException;

import de.uka.ilkd.key.nui.ViewInformation;
import de.uka.ilkd.key.nui.ViewPosition;

/**
 * TODO add class comment
 * 
 * @author
 * @version 1.0
 */
public class SerializableViewInformation {

    private String fxmlUrl;

    // TODO add documentation
    public String getFxmlUrl() {
        return fxmlUrl;
    }

    private boolean isactive;

    // TODO add documentation
    public boolean getIsActibe() {
        return isactive;
    }

    private ViewPosition viewPosition;

    // TODO add documentation
    public ViewPosition getViewPosition() {
        return viewPosition;
    }

    /**
     * TODO add comments
     * 
     * @param view
     */
    public SerializableViewInformation(ViewInformation view) {
        viewPosition = view.getCurrentPosition();
        isactive = view.getIsActive();
        fxmlUrl = view.getFxmlPath().getPath();
    }

    // TODO add documentation
    public String getSerialized() {
        return fxmlUrl + "," + viewPosition.toString() + "," + isactive;
    }

    /**
     * TODO add comments
     * 
     * @param data
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
