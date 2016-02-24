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

    private Criteria<Pair<Integer, String>> criteria;
    private FilterLayout layout;

    public FilterChangedEventArgs(FilterLayout layout,
            Criteria<Pair<Integer, String>> criteria) {
        this.layout = layout;
        this.criteria = criteria;
    }

    /**
     * The full criteria of the new filter.
     * @return
     */
    public Criteria<Pair<Integer, String>> getCriteria() {
        return criteria;
    }

    /**
     * The Layout of the new filter
     * @return
     */
    public FilterLayout getLayout() {
        return layout;
    }
}
