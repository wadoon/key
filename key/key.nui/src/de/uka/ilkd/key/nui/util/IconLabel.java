package de.uka.ilkd.key.nui.util;

import javafx.scene.control.Label;

public class IconLabel extends Label{
    public IconLabel(String cssIconId) {
        getStyleClass().add(cssIconId);
    }
}
