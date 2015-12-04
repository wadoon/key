package de.uka.ilkd.key.nui;

import java.net.URL;
import java.util.Observable;

public class ViewInformation extends Observable {

    public ViewInformation(String title, URL pathToFxml,
            ViewPosition preferedPosition) {
        fxmlPath = pathToFxml;
        this.preferedPosition = preferedPosition;
        currentPosition = preferedPosition;
        this.title = title;
    }

    private URL fxmlPath;

    public URL getFxmlPath() {
        return fxmlPath;
    }

    private String title;

    public String getTitle() {
        return title;
    }

    private boolean isActive = false;

    public boolean getIsActive() {
        return isActive;
    }

    public void setIsActive(boolean value) {
        if (isActive == value)
            return;
        isActive = value;
        this.setChanged();
        this.notifyObservers(true);
    }

    private ViewPosition preferedPosition;

    public ViewPosition getPreferedPosition() {
        return preferedPosition;
    }

    private ViewPosition currentPosition;

    public ViewPosition getCurrentPosition() {
        return currentPosition;
    }

    public void setCurrentPosition(ViewPosition position) {
        if (currentPosition == position)
            return;
        currentPosition = position;
        this.setChanged();
        this.notifyObservers(false);
    }
}
