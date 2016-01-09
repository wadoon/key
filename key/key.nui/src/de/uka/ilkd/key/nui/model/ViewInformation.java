package de.uka.ilkd.key.nui.model;

import java.io.IOException;
import java.net.URL;
import java.util.Observable;

import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.util.KeyFxmlLoader;
import de.uka.ilkd.key.nui.view.menu.ViewContextMenuController;
import javafx.fxml.FXMLLoader;
import javafx.geometry.Side;
import javafx.scene.Node;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.Tab;
import javafx.scene.input.ClipboardContent;
import javafx.scene.input.Dragboard;
import javafx.scene.input.MouseButton;
import javafx.scene.input.TransferMode;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Pane;

public class ViewInformation extends Observable {

    private int id;
    public int getId(){
        return id;
    }
    
    private static int nextId = 0;
    private static int getNextId(){
        return nextId++;
    }
    
    public ViewInformation(String title, URL pathToFxml,
            ViewPosition preferedPosition, boolean hasMenuItem) {
        fxmlPath = pathToFxml;
        this.preferedPosition = preferedPosition;
        currentPosition = preferedPosition;
        this.title = title;
        this.hasMenuItem = hasMenuItem;
        id = getNextId();
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
    
    private Tab uiTab = null;
    public Tab getUiTab(){
        return uiTab;
    }
    
    public void loadUiTab(ViewController parent){
        uiTab = createTab(this, parent.loadFxmlFromContext(getFxmlPath()),parent);   
    }
    
    /**
     * 
     * @param title
     * @param node
     * @return a tab with content node and title as lable, also drag
     *         functionality
     */
    private Tab createTab(ViewInformation view, Node node,ViewController parent) {
        Tab t = new Tab();
        Label title = new Label(view.getTitle());
        BorderPane header = new BorderPane();
        header.setCenter(title);
        t.setGraphic(header);
        t.setContent(node);

        header.setOnDragDetected(event -> {
            Dragboard db = header.startDragAndDrop(TransferMode.MOVE);
            ClipboardContent content = new ClipboardContent();
            content.putString(Integer.toString(view.getId()));
            db.setContent(content);
            event.consume();
        });

        t.setOnCloseRequest(event -> {
            view.setIsActive(false);
        });

        header.setOnMouseClicked(event -> {
            if (event.getButton() == MouseButton.SECONDARY)
                loadViewContextMenu(view,parent).show(title, Side.TOP, event.getX(),
                        event.getY());
        });

        return t;
    }
    
    private ContextMenu loadViewContextMenu(ViewInformation view,ViewController parent) {
        FXMLLoader loader = new FXMLLoader();
        loader.setLocation(ViewContextMenuController.class
                .getResource("ViewContextMenu.fxml"));
        ContextMenu content;
        try {
            content = loader.load();
        }
        catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
            return null;
        }

        // Give the controller access to the main app.
        ViewContextMenuController controller = loader.getController();
        controller.setMainApp(parent.getMainApp(), parent.getContext());
        controller.setParentView(view);
        content.setOnShowing((event) -> {
            // select current position
        });
        return content;
    }
}
