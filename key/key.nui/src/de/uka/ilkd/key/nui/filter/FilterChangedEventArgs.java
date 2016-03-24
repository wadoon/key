package de.uka.ilkd.key.nui.filter;

/**
 * EventArgs that contain all important information that should be revealed to
 * any listener.
 * 
 * @author Benedikt Gross
 * @version 1.0
 */
public class FilterChangedEventArgs {

    private PrintFilter filter;

    public FilterChangedEventArgs(PrintFilter filter) {
        this.filter = filter;
    }

    /**
     * @return the new filter
     */
    public PrintFilter getFilter() {
        return filter;
    }
}
