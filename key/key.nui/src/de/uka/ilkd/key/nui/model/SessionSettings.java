package de.uka.ilkd.key.nui.model;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.prefs.Preferences;

import com.sun.javafx.stage.ScreenHelper.ScreenAccessor;

import javafx.collections.ObservableList;
import javafx.geometry.Rectangle2D;
import javafx.stage.Screen;

public class SessionSettings {

    private static final int MinWidth = 50;
    private static final int MinHeight = 50;

    public SessionSettings() {
        views = new LinkedList<>();
    }

    private boolean corrupted = false;

    /**
     * Returns true if the set position does not fit on any screen and the
     * default bounds should be used.
     */
    public boolean getIsCorrupted() {
        return corrupted;
    }

    private List<ViewInformation> views;

    public List<ViewInformation> getViews() {
        return views;
    }

    public void setViews(List<ViewInformation> value) {
        views = value;
    }

    private List<Double> splitterPositions;

    public void setSplitterPositions(double leftVertical, double leftHorizontal,
            double rightVertical, double rightHorizontal) {
        splitterPositions = Arrays.asList(leftVertical, leftHorizontal,
                rightVertical, rightHorizontal);
    }

    public void setSplitterPositions(List<Double> list) {
        if (list.size() == 4)
            splitterPositions = list;
    }

    /**
     * size = 4 : left-vertical, left-horizontal, right-vertical,
     * right-horizontal
     */
    public List<Double> getSplitterPositions() {
        return splitterPositions;
    }

    private double windowX;

    public void setWindowX(double value) {
        windowX = value;
        CheckBounds();
    }

    public double getWindowX() {
        return windowX;
    }

    private double windowY;

    public void setWindowY(double value) {
        windowY = value;
        CheckBounds();
    }

    public double getWindowY() {
        return windowY;
    }

    private double windowHeight;

    public void setWindowHeight(double value) {
        if (value >= MinHeight)
            windowHeight = value;
        else
            windowHeight = MinHeight;
        CheckBounds();
    }

    public double getWindowHeight() {
        return windowHeight;
    }

    private double windowWidth;

    public void setWindowWidth(double value) {
        if (value >= MinWidth)
            windowWidth = value;
        else
            windowWidth = MinWidth;

        CheckBounds();
    }

    public double getWindowWidth() {
        return windowWidth;
    }

    /**
     * Keeps the Window visible
     */
    private void CheckBounds() {
        // get screens for x and y position
        List<Screen> containers = Screen.getScreensForRectangle(windowX,
                windowY, 1, 1);
        if (containers.size() > 0) {
            for (Screen s : containers) {
                if (s.getVisualBounds().contains(windowX, windowY, windowWidth,
                        windowHeight))
                    corrupted = false;
                return;
            }
            // if no screen contained the bounds, use default (= set corrupted)
            corrupted = true;
        }
        corrupted = true;
    }

    public void SaveAsLast() {
        if (corrupted)
            return;

        Preferences prefs = Preferences
                .userNodeForPackage(SessionSettings.class);
        prefs.putDouble("windowHeight", windowHeight);
        prefs.putDouble("windowWidth", windowWidth);
        prefs.putDouble("windowX", windowX);
        prefs.putDouble("windowY", windowY);
        prefs.putDouble("splitterLV", splitterPositions.get(0));
        prefs.putDouble("splitterLH", splitterPositions.get(1));
        prefs.putDouble("splitterRV", splitterPositions.get(2));
        prefs.putDouble("splitterRH", splitterPositions.get(3));
    }

    public static SessionSettings loadLastSettings() {
        SessionSettings settings = new SessionSettings();

        Preferences prefs = Preferences
                .userNodeForPackage(SessionSettings.class);
        settings.windowHeight = prefs.getDouble("windowHeight", -1);
        settings.windowWidth = prefs.getDouble("windowWidth", -1);
        settings.windowX = prefs.getDouble("windowX", -1);
        settings.windowY = prefs.getDouble("windowY", -1);
        settings.splitterPositions = Arrays.asList(prefs.getDouble("splitterLV", -1),
                prefs.getDouble("splitterLH", -1),
                prefs.getDouble("splitterRV", -1),
                prefs.getDouble("splitterRH", -1));
        settings.CheckBounds();
        return settings;
    }
}
