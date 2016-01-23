package de.uka.ilkd.key.nui.model;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.nui.ViewPosition;

public class SessionSettings {

    private static final int MinWidth = 50;
    private static final int MinHeight = 50;
    private static List<Integer> screenResolutionX;
    private static List<Integer> screenResolutionY;
    
    public SessionSettings() {
        screenResolutionX = new LinkedList<Integer>();
        //TODO
        screenResolutionY = new LinkedList<Integer>();
        //TODO
    }

    private Map<ViewPosition,List<ViewInformation>> views;
    public void setViews(Map<ViewPosition,List<ViewInformation>> value){
        views = value;
    }
    public Map<ViewPosition, List<ViewInformation>> getViews() {
        return views;
    }

    private List<Integer> splitterPositions;
    public void setSplitterPositions(List<Integer> value){
        splitterPositions = value;
    }
    
    // 4: left-horizontal,right-horizontal, left-vertical, right-vertical
    public List<Integer> getSplitterPositions() {
        return splitterPositions;
    }

    private int windowX;
    public void setWindowX(int value) {
        if(value >= 0)
        windowX = value;
        else if(value > screenResolutionX.get(lastUsedScreen))
            windowX = screenResolutionX.get(lastUsedScreen);
        else windowX = 0;
    }
    public int getWindowX() {
        return windowX;
    }

    private int windowY;
    public void setWindowY(int value){
        if(value >= 0)
        windowY = value;
        else if(value > screenResolutionY.get(lastUsedScreen))
            windowY = screenResolutionY.get(lastUsedScreen);
        else windowY = 0;
    }
    public int getWindowY() {
        return windowY;
    }

    private int windowHeight;
    public void setWindowHeight(int value){
        if(value >= 0)
        windowHeight=value;
        else windowHeight = MinHeight;
    }
    public int getWindowHeight() {
        return windowHeight;
    }

    private int windowWidth;
    public void setWindowWidth(int value){
        if(value >= 50)
        windowWidth=value;
        else windowWidth = MinWidth;
    }
    public int getWindowWidth() {
        return windowWidth;
    }

    private int lastUsedScreen;
    public void setLastUsedScreen(int value){
        lastUsedScreen = value;
    }
    public int getLastUsedScreen() {
        return lastUsedScreen;
    }
    
    public void Save(){
        
    }
    
    public static SessionSettings loadLastSettings(){
        return null;
    }
}
