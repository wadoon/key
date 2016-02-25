package de.uka.ilkd.key.nui.filter;

import de.uka.ilkd.key.util.Pair;

/**
 * A class that handles all information needed to create a criteria for
 * sequent-filtering and also stores information related to the layout of
 * filtered lines.
 * 
 * @author Benedikt Gross
 *
 */
public class PrintFilter {

    private String name;

    /**
     * Name used to save this filter.
     * 
     * @return
     */
    public String getName() {
        return name;
    }

    /**
     * Name used to save this filter.
     * 
     * @return
     */
    public void setName(String value) {
        name = value;
        // no need to notify observer since the name is only for storage
    }

    private String searchText;

    /**
     * The text that should be filtered for.
     */
    public void setSearchText(String value) {
        searchText = value;
    }

    /**
     * The text that should be filtered for.
     * 
     * @return
     */
    public String getSearchText() {
        return searchText;
    }

    private Criteria<Pair<Integer, String>> selectionCriteria;

    /**
     * A criteria representing a selection on the sequent.
     */
    public void setSelectionCriteria(Criteria<Pair<Integer, String>> value) {
        if (value == selectionCriteria)
            return;
        selectionCriteria = value;
    }

    /**
     * A criteria representing a selection on the sequent.
     */
    public Criteria<Pair<Integer, String>> getSelectionCriteria() {
        return selectionCriteria;
    }

    private boolean isUserCriteria;

    /**
     * A value that indicates if a selection is used, or a search text with
     * custom data.
     */
    public boolean getIsUserCriteria() {
        return isUserCriteria;
    }

    /**
     * A value that indicates if a selection is used, or a search text with
     * custom data.
     */
    public void setIsUserCriteria(boolean value) {
        if (isUserCriteria == value)
            return;
        isUserCriteria = value;
    }

    private int before;

    public int getBefore() {
        return before;
    }

    public void setBefore(int value) {
        if (value == before)
            return;
        before = value;
    }

    private int after;

    public int getAfter() {
        return after;
    }

    public void setAfter(int value) {
        if (after == value)
            return;
        after = value;
    }

    private boolean invert;

    /**
     * Indicates whether the filter should be inverted.
     */
    public void setInvert(boolean value) {
        invert = value;
    }

    /**
     * Indicates whether the filter should be inverted.
     */
    public boolean getInvert() {
        return invert;
    }

    private boolean useAstScope;

    /**
     * Indicates whether before/after should apply to lines or ast elements.
     */
    public void setUseAstScope(boolean value) {
        useAstScope = value;
    }

    /**
     * Indicates whether before/after should apply to lines or ast elements.
     */
    public boolean getUseAstScope() {
        return useAstScope;
    }

    private FilterLayout filterLayout;

    public FilterLayout getFilterLayout() {
        return filterLayout;
    }

    public void setFilterLayout(FilterLayout value) {
        if (filterLayout == value)
            return;
        filterLayout = value;
    }

    public PrintFilter() {
        isUserCriteria = true;
        selectionCriteria = new CriterionEmpty<Pair<Integer, String>>();
        before = 2;
        after = 2;
        filterLayout = FilterLayout.Minimize;
    }

    public PrintFilter cloneFilter() {
        PrintFilter filter = new PrintFilter();
        filter.setName(this.name);
        filter.setSelectionCriteria(this.selectionCriteria);
        filter.setIsUserCriteria(this.isUserCriteria);
        filter.setSearchText(this.searchText);
        filter.setInvert(this.invert);
        filter.setAfter(this.after);
        filter.setBefore(this.before);
        filter.setFilterLayout(this.filterLayout);
        filter.setUseAstScope(this.useAstScope);
        return filter;
    }

    public enum FilterLayout {
        Collapse, Minimize
    }
}
