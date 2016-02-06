package de.uka.ilkd.key.nui.model;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.prefs.Preferences;

import de.uka.ilkd.key.nui.util.SerializableViewInformation;
import javafx.collections.ObservableList;
import javafx.geometry.Rectangle2D;
import javafx.stage.Screen;
import javafx.stage.Stage;

public class SessionSettings {

    private static final int MinWidth = 300;
    private static final int MinHeight = 200;

    private boolean boundsCorrupted = false;

    /**
     * Returns true if the set position does not fit on any screen and the
     * default bounds should be used.
     */
    public boolean getBoundsIsCorrupted() {
        return boundsCorrupted;
    }

    private List<SerializableViewInformation> views = new LinkedList<>();

    public List<SerializableViewInformation> getViews() {
        return views;
    }

    public void setViews(List<ViewInformation> viewInformations) {
        views = new LinkedList<>();
        for (ViewInformation view : viewInformations) {
            views.add(new SerializableViewInformation(view));
        }
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
        // CheckBounds();
    }

    public double getWindowX() {
        return windowX;
    }

    private double windowY;

    public void setWindowY(double value) {
        windowY = value;
        // CheckBounds();
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
        // CheckBounds();
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

        // CheckBounds();
    }

    public double getWindowWidth() {
        return windowWidth;
    }

    /**
     * Keeps the Window visible
     */
    private void CheckBounds() {
        // workaround for JavaFx malfunction that causes x and y to be slightly
        // negative
        if (windowX < 0)
            windowX = 0;
        if (windowY < 0)
            windowY = 0;

        // get screens for x and y position (regardless of size)
        List<Screen> containers = Screen.getScreensForRectangle(windowX,
                windowY, 1, 1);
        if (containers.size() > 0) {
            for (Screen s : containers) {
                // make sure 75% of the window is on the screen
                if (s.getBounds().contains(windowX, windowY, windowWidth * 0.75,
                        windowHeight * 0.75)) {
                    boundsCorrupted = false;
                    return;
                }
            }
        }
        boundsCorrupted = true;
    }

    public void SaveAsLast() {
        CheckBounds();
        if (boundsCorrupted)
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
        StringBuilder viewBuilder = new StringBuilder();
        views.forEach(sv -> viewBuilder.append(sv.getSerialized() + ";"));
        prefs.put("views", viewBuilder.toString());
    }

    public static SessionSettings loadLastSettings() {
        try {
            SessionSettings settings = new SessionSettings();
            Preferences prefs = Preferences
                    .userNodeForPackage(SessionSettings.class);
            settings.windowHeight = prefs.getDouble("windowHeight", -1);
            settings.windowWidth = prefs.getDouble("windowWidth", -1);
            settings.windowX = prefs.getDouble("windowX", -1);
            settings.windowY = prefs.getDouble("windowY", -1);
            settings.splitterPositions = Arrays.asList(
                    prefs.getDouble("splitterLV", -1),
                    prefs.getDouble("splitterLH", -1),
                    prefs.getDouble("splitterRV", -1),
                    prefs.getDouble("splitterRH", -1));
            settings.CheckBounds();
            settings.views = new LinkedList<>();
            for (String vinfostr : prefs.get("views", "").split(";")) {
                if (vinfostr == null || vinfostr.isEmpty())
                    continue;
                settings.views.add(new SerializableViewInformation(vinfostr));
            }
            return settings;
        }
        catch (Exception ex) {
            ex.printStackTrace();
            System.out.println(
                    "Error while loading Gui Settings - using defaults");
            return null;
        }
    }
}
