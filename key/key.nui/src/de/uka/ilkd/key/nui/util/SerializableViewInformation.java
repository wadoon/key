package de.uka.ilkd.key.nui.util;

import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.ViewInformation;

public class SerializableViewInformation {

    private String fxmlUrl;
    public String getFxmlUrl(){
        return fxmlUrl;
    }
    
    private boolean isactive;
    public boolean getIsActibe(){
        return isactive;
    }
    
    private ViewPosition viewPosition;
    public ViewPosition getViewPosition(){
        return viewPosition;
    }
    
    public SerializableViewInformation(ViewInformation view) {
        viewPosition = view.getCurrentPosition();
        isactive = view.getIsActive();
        fxmlUrl = view.getFxmlPath().getPath();
    }
    
    public String getSerialized(){
        return fxmlUrl + "," + viewPosition.toString() + "," + isactive;
    }
    
    public SerializableViewInformation(String data){
        String[] dataArr = data.split(",");
        fxmlUrl = dataArr[0];
        viewPosition = Enum.valueOf(ViewPosition.class, dataArr[1]);
        isactive = Boolean.parseBoolean(dataArr[2]);
    }
}
