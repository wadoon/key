package playground.richtextFX;

import java.net.URL;

import javafx.scene.input.KeyCombination;

public interface IViewContainer {
    /**
     * Registers a view for displaying and adds a new menu entry in the "views" menu
     * @param title Text of the menu entry
     * @param path Url to the fxml file of the view
     * @param preferredPosition Position in which the view is displayed as default
     * @param keys Shortcut
     */
    public void registerView(String title,URL path, ViewPosition preferredPosition, String accelerator);
}
