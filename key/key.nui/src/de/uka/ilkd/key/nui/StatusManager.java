package de.uka.ilkd.key.nui;

import de.uka.ilkd.key.nui.event.HandlerEvent;
import de.uka.ilkd.key.nui.util.TipOfTheDay;

/**
 * This class supplies managed access to the status-bar on the UI.
 * 
 * @author Benedikt Gross
 * @version 1.0
 */
public class StatusManager {
    private HandlerEvent<String> statusUpdatedEvent = new HandlerEvent<String>();

    /**
     * An event that is fired each time a new status is set.
     * 
     * @return Status updated event.
     */
    public HandlerEvent<String> getStatusUpdatedEvent() {
        return statusUpdatedEvent;
    }

    private String status = null;

    /**
     * Shows a status on the status-bar of the UI.
     * 
     * @param status
     *            Status to be shown.
     */
    public void setStatus(String status) {
        if (status == null || this.status.equals(status))
            return;
        this.status = status;
        statusUpdatedEvent.fire(status);
    }

    /**
     * Replaces the current status on the status bar to show a hint about using
     * KeY.
     */
    public void resetStatus() {
        status = "Hint: " + TipOfTheDay.get();
        statusUpdatedEvent.fire(status);
    }

    /**
     * Returns the current status that is currently displayed in the status-bar.
     * 
     * @return Current status.
     */
    public String getStatus() {
        return status;
    }
}
