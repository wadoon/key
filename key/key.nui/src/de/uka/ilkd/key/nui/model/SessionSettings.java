package de.uka.ilkd.key.nui.model;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

public class SessionSettings {

    private static final int MinWidth = 50;
    private static final int MinHeight = 50;
    private static List<Integer> screenResolutionX;
    private static List<Integer> screenResolutionY;

    public SessionSettings() {
        screenResolutionX = new LinkedList<Integer>();
        screenResolutionY = new LinkedList<Integer>();
        views = new LinkedList<>();
    }

    private List<ViewInformation> views;

    public List<ViewInformation> getViews() {
        return views;
    }

    public void setViews(List<ViewInformation> value) {
        views = value;
    }

    private List<Integer> splitterPositions;

    public void setSplitterPositions(int leftVertical, int leftHorizontal,
            int rightVertical, int rightHorizontal) {
        splitterPositions = Arrays.asList(leftVertical, leftHorizontal,
                rightVertical, rightHorizontal);
    }

    /**
     * size = 4 : left-vertical, left-horizontal, right-vertical, right-horizontal
     */
    public List<Integer> getSplitterPositions() {
        return splitterPositions;
    }

    private int windowX;

    public void setWindowX(int value) {
        windowX = value;
        CheckXPosition();
    }

    public int getWindowX() {
        return windowX;
    }

    private int windowY;

    public void setWindowY(int value) {
        windowY = value;
        CheckYPosition();
    }

    public int getWindowY() {
        return windowY;
    }

    private int windowHeight;

    public void setWindowHeight(int value) {
        if (value >= MinHeight)
            windowHeight = value;
        else
            windowHeight = MinHeight;
        CheckYPosition();
    }

    public int getWindowHeight() {
        return windowHeight;
    }

    private int windowWidth;

    public void setWindowWidth(int value) {
        if (value >= MinWidth)
            windowWidth = value;
        else
            windowWidth = MinWidth;

        CheckXPosition();
    }

    public int getWindowWidth() {
        return windowWidth;
    }

    private int lastUsedScreen;

    public void setLastUsedScreen(int value) {
        lastUsedScreen = value;
    }

    public int getLastUsedScreen() {
        return lastUsedScreen;
    }

    /**
     * Keeps the Window visible
     */
    private void CheckYPosition() {
        if (windowY < 0)
            windowY = 0;
        else if (windowY > screenResolutionY.get(lastUsedScreen) - windowHeight)
            windowY = screenResolutionY.get(lastUsedScreen) - windowHeight;
        // else leave the value as it is
    }

    /**
     * Keeps the Window visible
     */
    private void CheckXPosition() {
        if (windowX < 0)
            windowX = 0;
        else if (windowX > screenResolutionX.get(lastUsedScreen) - windowWidth)
            windowX = screenResolutionX.get(lastUsedScreen) - windowWidth;
        // else leave the value as it is
    }

    public void Save() {

    }

    public static SessionSettings loadLastSettings() {
        return null;
    }
}
