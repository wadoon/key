package de.uka.ilkd.key.nui;

import de.uka.ilkd.key.nui.util.CsEvent;

public class StatusManager {
    private CsEvent<String> statusUpdatedEvent = new CsEvent<String>();
    public CsEvent<String> getStatusUpdatedEvent(){
        return statusUpdatedEvent;
    }
    
    private String status;
    public void setStatus(String status) {
        this.status = status;
        statusUpdatedEvent.fire(status);
    }
    public void clearStatus() {
        status = "";
        statusUpdatedEvent.fire(status);
    }
    
    public String getStatus(){
        return status;
    }
}
