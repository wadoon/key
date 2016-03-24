package de.uka.ilkd.key.nui;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.prefs.Preferences;
import de.uka.ilkd.key.nui.util.SerializableViewInformation;
import javafx.stage.Screen;

/**
 * Class for storage of window position, view position, layout etc.
 * 
 * @author Benedikt Gross
 * @version 1.0
 */
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

    /**
     * @return a list of all stored {@link SerializableViewInformation
     *         SerializableViewInformations}
     */
    public List<SerializableViewInformation> getViews() {
        return views;
    }

    /**
     * Sets the values to store as the {@link SerializableViewInformation
     * SerializableViewInformations}.
     * 
     * @param viewInformations
     *            the {@link SerializableViewInformation
     *            SerializableViewInformations} to store.
     */
    public void setViews(List<ViewInformation> viewInformations) {
        views = new LinkedList<>();
        for (ViewInformation view : viewInformations) {
            views.add(new SerializableViewInformation(view));
        }
    }

    private List<Double> splitterPositions;

    /**
     * Sets the values to store as the position of all SplitPane dividers.
     * 
     * @param leftVertical
     *            the relative position of the left of the two vertical dividers
     * @param leftHorizontal
     *            the relative position of the left of the two horizontal
     *            dividers
     * @param rightVertical
     *            the relative position of the right of the two vertical
     *            dividers
     * @param rightHorizontal
     *            the relative position of the right of the two horizontal
     *            dividers
     */
    public void setSplitterPositions(double leftVertical, double leftHorizontal,
            double rightVertical, double rightHorizontal) {
        splitterPositions = Arrays.asList(leftVertical, leftHorizontal,
                rightVertical, rightHorizontal);
    }

    /**
     * Sets the values to store as the position of all SplitPane dividers if the
     * given list is of size 4.
     * 
     * @param list
     *            List of divider positions in the order: leftVertical,
     *            leftHorizontal, rightVertical, rightHorizontal. Nothing will
     *            happen is the given list is not of size 4.
     */
    public void setSplitterPositions(List<Double> list) {
        if (list.size() == 4)
            splitterPositions = list;
    }

    /**
     * @return list of size 4 of relative devider positions: left-vertical,
     *         left-horizontal, right-vertical, right-horizontal
     */
    public List<Double> getSplitterPositions() {
        return splitterPositions;
    }

    private double windowX;

    /**
     * Sets the value to store as the window's x position.
     * 
     * @param value
     *            the x position.
     */
    public void setWindowX(double value) {
        windowX = value;
    }

    /**
     * @return the stored window's x position.
     */
    public double getWindowX() {
        return windowX;
    }

    private double windowY;

    /**
     * Sets the value to store as the window's y position.
     * 
     * @param value
     *            the y position.
     */
    public void setWindowY(double value) {
        windowY = value;
    }

    /**
     * @return the stored window's y position
     */
    public double getWindowY() {
        return windowY;
    }

    private double windowHeight;

    /**
     * Sets the value to store as the window's height or its min height,
     * whatever is of greater value.
     * 
     * @param value
     *            the window height.
     */
    public void setWindowHeight(double value) {
        if (value >= MinHeight)
            windowHeight = value;
        else
            windowHeight = MinHeight;
    }

    /**
     * @return the stored window height
     */
    public double getWindowHeight() {
        return windowHeight;
    }

    private double windowWidth;

    /**
     * Sets the value to store as the window's width or its min width, whatever
     * is of greater value.
     * 
     * @param value
     *            the window width.
     */
    public void setWindowWidth(double value) {
        if (value >= MinWidth)
            windowWidth = value;
        else
            windowWidth = MinWidth;

    }

    /**
     * @return the stored window width
     */
    public double getWindowWidth() {
        return windowWidth;
    }

    /**
     * Keeps the Window visible
     */
    private void checkBounds() {
        // workaround for JavaFx malfunction that causes x and y to be slightly
        // negative
        if (windowX < 0)
            windowX = 0;
        if (windowY < 0)
            windowY = 0;

        // catch negative size, because bounds.contains does not handle this
        if (windowHeight < 0 || windowWidth < 0) {
            boundsCorrupted = true;
            return;
        }

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

    /**
     * Saves the current settings to preferences so it can be loaded when the
     * application is started the next time.
     */
    public void saveAsLast() {
        checkBounds();
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

    /**
     * @return the last saved SessionSettings 
     */
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
            settings.checkBounds();
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
