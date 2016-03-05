package de.uka.ilkd.key.nui;

import de.uka.ilkd.key.nui.event.HandlerEvent;

public class StatusManager {
    private HandlerEvent<String> statusUpdatedEvent = new HandlerEvent<String>();
    public HandlerEvent<String> getStatusUpdatedEvent(){
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
