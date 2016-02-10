package de.uka.ilkd.key.nui.filter;

public class SelectModeEventArgs {
    private FilterSelection filterSelection;

    public SelectModeEventArgs(FilterSelection filterSelection) {
        this.filterSelection = filterSelection;
    }

    public FilterSelection getFilterSelection() {
        return filterSelection;
    }
}
