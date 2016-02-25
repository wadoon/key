package de.uka.ilkd.key.nui.filter;

import de.uka.ilkd.key.nui.filter.PrintFilter.FilterLayout;
import de.uka.ilkd.key.util.Pair;

/**
 * EventArgs that contain all important information that should be revealed to
 * any listener.
 * 
 * @author Benedikt Gross
 *
 */
public class FilterChangedEventArgs {

    private PrintFilter filter;

    public FilterChangedEventArgs(PrintFilter filter) {
        this.filter = filter;
    }

    /**
     * The new filter
     * @return
     */
    public PrintFilter getFilter() {
        return filter;
    }
}
