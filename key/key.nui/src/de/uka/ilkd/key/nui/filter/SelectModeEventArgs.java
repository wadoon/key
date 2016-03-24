package de.uka.ilkd.key.nui.filter;

/**
 * Provides information for a triggered filter selection.
 * 
 * @author Benedikt Gross
 * @version 1.0
 */
public class SelectModeEventArgs {
    private FilterSelection filterSelection;

    /**
     * @param filterSelection
     *            An object that contains all information for one selection
     *            workflow.
     */
    public SelectModeEventArgs(FilterSelection filterSelection) {
        this.filterSelection = filterSelection;
    }

    /**
     * @return The data object
     */
    public FilterSelection getFilterSelection() {
        return filterSelection;
    }
}
