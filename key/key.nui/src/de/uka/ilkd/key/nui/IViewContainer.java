package de.uka.ilkd.key.nui;

import java.net.URL;

import javafx.scene.input.KeyCombination;

public interface IViewContainer {
    public void registerView(String title,URL path, ViewPosition preferredPosition, KeyCombination keys);
    public void registerView(String title,URL path, ViewPosition preferredPosition);
}
