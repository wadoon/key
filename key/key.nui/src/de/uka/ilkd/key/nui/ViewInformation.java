package de.uka.ilkd.key.nui;

import java.io.IOException;
import java.net.URL;
import java.util.Observable;

import de.uka.ilkd.key.nui.view.menu.ViewContextMenuController;
import javafx.fxml.FXMLLoader;
import javafx.geometry.Side;
import javafx.scene.Node;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.Tab;
import javafx.scene.control.Tooltip;
import javafx.scene.input.ClipboardContent;
import javafx.scene.input.Dragboard;
import javafx.scene.input.MouseButton;
import javafx.scene.input.TransferMode;
import javafx.util.Pair;

public class ViewInformation extends Observable {

    private int id;

    public int getId() {
        return id;
    }

    private static int nextId = 0;

    private static int getNextId() {
        return nextId++;
    }

    private boolean hasMenuItem;

    public boolean hasMenuItem() {
        return hasMenuItem;
    }

    private URL fxmlPath;

    public URL getFxmlPath() {
        return fxmlPath;
    }

    private String title;

    public String getTitle() {
        return title;
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

    private Tab uiTab = null;

    public Tab getUiTab() {
        return uiTab;
    }

    private ViewController controller;

    public ViewController getController() {
        return controller;
    }

    public ViewInformation(String title, URL pathToFxml, ViewPosition preferedPosition, boolean hasMenuItem) {
        fxmlPath = pathToFxml;
        this.preferedPosition = preferedPosition;
        currentPosition = preferedPosition;
        this.title = title;
        this.hasMenuItem = hasMenuItem;
        id = getNextId();
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

    public void loadUiTab(ViewController parent) {
        Pair<Object, ViewController> pair = parent.loadFxmlViewController(getFxmlPath());
        uiTab = createTab((Node) pair.getKey(), parent);
        controller = pair.getValue();
    }

    /**
     * 
     * @param node
     * @param parent
     * @return a tab with content node and title as label, also drag
     *         functionality
     */
    private Tab createTab(Node node, ViewController parent) {
        Tab tab = new Tab();
        String title = getTitle();
        // t.setText(title);
        Label titleLabel = new Label(title);
        // BorderPane header = new BorderPane();
        // header.setCenter(titleLabel);
        tab.setGraphic(titleLabel);
        tab.setContent(node);
        tab.setTooltip(new Tooltip("Drag\u0026Drop or Right-Click to move Tab"));

        titleLabel.setOnDragDetected(event -> {
            if (event.getButton() != MouseButton.PRIMARY)
                return;
            Dragboard db = titleLabel.startDragAndDrop(TransferMode.MOVE);
            ClipboardContent content = new ClipboardContent();
            content.putString(Integer.toString(this.getId()));
            db.setContent(content);
            event.consume();
        });

        tab.setOnCloseRequest(event -> {
            this.setIsActive(false);
        });

        titleLabel.setOnMouseClicked(event -> {
            if (event.getButton() == MouseButton.SECONDARY)

                loadViewContextMenu(parent).show(titleLabel, Side.TOP, event.getX(), event.getY());
        });

        return tab;
    }

    private ContextMenu loadViewContextMenu(ViewController parent) {
        FXMLLoader loader = new FXMLLoader();
        loader.setLocation(ViewContextMenuController.class.getResource("ViewContextMenu.fxml"));
        ContextMenu content;
        try {
            content = loader.load();
        }
        catch (IOException e) {
            e.printStackTrace();
            return null;
        }

        // Give the controller access to the main app.
        ViewContextMenuController controller = loader.getController();
        controller.initViewController(parent.getMainApp(), parent.getContext());
        controller.setParentView(this);
        content.setOnShowing((event) -> {
            // TODO select current position
        });
        return content;
    }
}
