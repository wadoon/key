package de.uka.ilkd.key.nui.filter;

import java.util.LinkedList;
import java.util.List;

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

    private List<String> selections;

    /**
     * A criteria representing a selection on the sequent.
     */
    public void setSelections(List<String> value) {
        if (value == selections)
            return;
        selections = value;
    }

    /**
     * A criteria representing a selection on the sequent.
     */
    public List<String> getSelections() {
        return selections;
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
        isUserCriteria = value;
    }

    private int before;

    /**
     * Indicates how many lines of the sequent should be displayed <b>before</b>
     * each filter match. (Ignored when ast-scope is used)
     */
    public int getBefore() {
        return before;
    }

    /**
     * Indicates how many lines of the sequent should be displayed <b>before</b>
     * each filter match. (Ignored when ast-scope is used)
     */
    public void setBefore(int value) {
        before = value;
    }

    private int after;

    /**
     * Indicates how many lines of the sequent should be displayed <b>after</b>
     * each filter match. (Ignored when ast-scope is used)
     */
    public int getAfter() {
        return after;
    }

    /**
     * Indicates how many lines of the sequent should be displayed <b>after</b>
     * each filter match. (Ignored when ast-scope is used)
     */
    public void setAfter(int value) {
        after = value;
    }

    private boolean invert;

    /**
     * Indicates whether the filter should be inverted. (Ignored when text-scope
     * is used)
     */
    public boolean getInvert() {
        return invert;
    }

    /**
     * Indicates whether the filter should be inverted. (Ignored when text-scope
     * is used)
     */
    public void setInvert(boolean value) {
        invert = value;
    }

    private boolean useAstScope;

    /**
     * Indicates whether before/after should apply to lines or an ast-scope
     * should be used instead.
     */
    public boolean getUseAstScope() {
        return useAstScope;
    }

    /**
     * Indicates whether before/after should apply to lines or an ast-scope
     * should be used instead.
     */
    public void setUseAstScope(boolean value) {
        useAstScope = value;
    }

    private FilterLayout filterLayout;

    /**
     * The {link FilterLayout} of the current filter.
     */
    public FilterLayout getFilterLayout() {
        return filterLayout;
    }

    /**
     * The {link FilterLayout} of the current filter.
     */
    public void setFilterLayout(FilterLayout value) {
        filterLayout = value;
    }

    public PrintFilter() {
        isUserCriteria = true;
        selections = new LinkedList<>();
        before = 2;
        after = 2;
        filterLayout = FilterLayout.Minimize;
    }

    public PrintFilter cloneFilter() {
        PrintFilter filter = new PrintFilter();
        filter.setName(this.name);
        filter.setSelections(this.selections);
        filter.setIsUserCriteria(this.isUserCriteria);
        filter.setSearchText(this.searchText);
        filter.setInvert(this.invert);
        filter.setAfter(this.after);
        filter.setBefore(this.before);
        filter.setFilterLayout(this.filterLayout);
        filter.setUseAstScope(this.useAstScope);
        return filter;
    }

    /**
     * Indicates how lines that did not match a filter should be displayed (
     * <b>hidden</b>).
     * 
     * @author Benedikt Gross
     *
     */
    public enum FilterLayout {
        /**
         * Each block of <b>hidden</b> lines will be collapsed to "..."
         */
        Collapse,

        /**
         * All <b>hidden</b> lines will be displayed with a smaller font.
         */
        Minimize
    }
}
