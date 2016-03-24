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

/**
 * This class aggregates all information about a view, including its UI tab,
 * FXML path, controller, menu item etc.
 * 
 * @author Benedikt Gross
 * @author Victor Schuemmer
 * @version 1.0
 */
public class ViewInformation extends Observable {

    private int id;

    /**
     * @return the unique (at least for this session) ID of this ViewInformation
     */
    public int getId() {
        return id;
    }

    private static int nextId = 0;

    private static int getNextId() {
        return nextId++;
    }

    private boolean hasMenuItem;

    /**
     * @return true iff this view has a menu item to show and hide it.
     */
    public boolean hasMenuItem() {
        return hasMenuItem;
    }

    private URL fxmlPath;

    /**
     * @return the path to the FXML of the view
     */
    public URL getFxmlPath() {
        return fxmlPath;
    }

    private String title;

    /**
     * @return the title of the view as displayed in the tab header
     */
    public String getTitle() {
        return title;
    }

    private ViewPosition preferredPosition;

    /**
     * @return the preferred @{link ViewPosition} of the view
     */
    public ViewPosition getPreferredPosition() {
        return preferredPosition;
    }

    private ViewPosition currentPosition;

    /**
     * @return the current {@link ViewPosition} of the view
     */
    public ViewPosition getCurrentPosition() {
        return currentPosition;
    }

    /**
     * Sets the {@link ViewPosition} of the view to the new position.
     * @param position the {@link ViewPosition} to set
     */
    public void setCurrentPosition(ViewPosition position) {
        if (currentPosition == position)
            return;
        currentPosition = position;
        this.setChanged();
        this.notifyObservers(false);
    }

    private Tab uiTab = null;

    /**
     * @return the tab the view is shown in
     */
    public Tab getUiTab() {
        return uiTab;
    }

    public void setTabTitle(String t) {
        title = t;
        uiTab.setGraphic(makeTitleLabel(parent));
    }

    private ViewController controller;

    /**
     * @return the {@link ViewController} of the view
     */
    public ViewController getController() {
        return controller;
    }

    /**
     * The constructor.
     * @param title The title of the view. This will be shown in the tab header.
     * @param pathToFxml the path to the FXML file
     * @param preferredPosition the preferred {@link ViewPosition}
     * @param hasMenuItem
     */
    public ViewInformation(String title, URL pathToFxml,
            ViewPosition preferredPosition, boolean hasMenuItem) {
        fxmlPath = pathToFxml;
        this.preferredPosition = preferredPosition;
        currentPosition = preferredPosition;
        this.title = title;
        this.hasMenuItem = hasMenuItem;
        id = getNextId();
    }

    private boolean isActive = false;

    /**
     * @return true iff the view is currently active
     */
    public boolean getIsActive() {
        return isActive;
    }

    /**
     * TODO add documentation
     */
    public void setIsActive(boolean value) {
        if (isActive == value)
            return;
        isActive = value;
        this.setChanged();
        this.notifyObservers(true);
    }

    private ViewController parent;

    public void loadUiTab(ViewController parent) {
        Pair<Object, ViewController> pair = parent
                .loadFxmlViewController(getFxmlPath());
        this.parent = parent;
        uiTab = createTab((Node) pair.getKey(), parent);
        controller = pair.getValue();
        controller.getTitleUpdatedEvent().addHandler(this::setTabTitle);
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
        tab.setGraphic(makeTitleLabel(parent));
        tab.setContent(node);
        tab.setTooltip(
                new Tooltip("Drag\u0026Drop or Right-Click to move Tab"));
        tab.setOnCloseRequest(event -> {
            this.setIsActive(false);
        });

        return tab;
    }

    private Label makeTitleLabel(ViewController parent) {
        Label titleLabel = new Label(title);

        titleLabel.setOnDragDetected(event -> {
            if (event.getButton() != MouseButton.PRIMARY)
                return;
            Dragboard db = titleLabel.startDragAndDrop(TransferMode.MOVE);
            ClipboardContent content = new ClipboardContent();
            content.putString(Integer.toString(this.getId()));
            db.setContent(content);
            event.consume();
        });

        titleLabel.setOnMouseClicked(event -> {
            if (event.getButton() == MouseButton.SECONDARY)
                loadViewContextMenu(parent).show(titleLabel, Side.TOP,
                        event.getX(), event.getY());
        });

        return titleLabel;
    }

    private ContextMenu loadViewContextMenu(ViewController parent) {
        FXMLLoader loader = new FXMLLoader();
        loader.setLocation(ViewContextMenuController.class
                .getResource("ViewContextMenu.fxml"));
        ContextMenu content;
        try {
            content = loader.load();
        }
        catch (IOException e) {
            e.printStackTrace();
            return null;
        }

        ViewContextMenuController controller = loader.getController();
        controller.setParentView(this);
        content.setOnShowing((event) -> {
            controller.selectPosition();
        });
        return content;
    }
}
