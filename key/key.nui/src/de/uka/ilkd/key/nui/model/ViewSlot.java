package de.uka.ilkd.key.nui.model;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.reference.ThisConstructorReference;
import de.uka.ilkd.key.nui.ViewPosition;
import javafx.scene.Node;
import javafx.scene.control.TabPane;
import javafx.scene.control.TabPane.TabClosingPolicy;
import javafx.scene.layout.Border;
import javafx.scene.layout.BorderPane;

public class ViewSlot {
    private List<ViewInformation> tabs = new LinkedList<>();
    private BorderPane uiPane;
    private boolean used = false;
    private ViewPosition position;
    
    public List<ViewInformation> getTabs(){
        return tabs;
    }
    public BorderPane getUiPane(){
        return uiPane;
    }
    public boolean getUsed(){
        return used;
    }
    
    public ViewSlot(ViewPosition position,BorderPane pane){
        this.position = position;
        uiPane = pane;
        currentRegisterer.accept(pane.getCenter());
    }
    
    public ViewPosition getViewPosition(){
        return position;
    }
    
    public void addTab(ViewInformation view){
        tabs.add(view);
        TabPane container =((TabPane)uiPane.getCenter());
        container.getTabs().add(view.getUiTab());
        container.setTabClosingPolicy(TabClosingPolicy.ALL_TABS);
        used = true;

        container.getSelectionModel().select(view.getUiTab());
    }
    
    public void removeTab(ViewInformation view){
        if(!((TabPane)uiPane.getCenter()).getTabs().contains(view.getUiTab()))
            System.out.println("NOOOOO!");
        ((TabPane)uiPane.getCenter()).getTabs().remove(view.getUiTab());
        tabs.remove(view);
        if(tabs.size() == 0)
            used = false;
    }
    
    private static java.util.function.Consumer<Node> currentRegisterer;
    public static void setRegisterDrag(java.util.function.Consumer<Node> registerer){
        currentRegisterer = registerer;
    }
}
