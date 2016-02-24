package de.uka.ilkd.key.nui.filter;

/**
 * Provides information for a triggered selection "mode"
 * @author Benedikt Gross
 *
 */
public class SelectModeEventArgs {
    private FilterSelection filterSelection;

    public SelectModeEventArgs(FilterSelection filterSelection) {
        this.filterSelection = filterSelection;
    }

    public FilterSelection getFilterSelection() {
        return filterSelection;
    }
}
