package de.uka.ilkd.key.nui.filter;

import java.util.LinkedList;
import java.util.List;
import java.util.Observable;

/**
 * A class that handles all information needed to create a criteria for
 * sequent-filtering and also stores information related to the layout of
 * filtered lines.
 * 
 * @author Benedikt Gross
 * @version 1.0
 */
public class PrintFilter extends Observable {

    private String searchText;

    /**
     * The text that should be filtered for.
     */
    public void setSearchText(String value) {
        if (searchText == null && value == null
                || searchText != null && searchText.equals(value))
            return;
        searchText = value;
        notifyChanged();
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
        notifyChanged();
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
        if (isUserCriteria == value)
            return;
        isUserCriteria = value;
        notifyChanged();
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
        if (before == value)
            return;
        before = value;
        notifyChanged();
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
        if (after == value)
            return;
        after = value;
        notifyChanged();
    }

    private boolean invert;

    /**
     * Indicates whether the filter should be inverted. (Ignored when not
     * ast-scope is used)
     */
    public boolean getInvert() {
        return invert;
    }

    /**
     * Indicates whether the filter should be inverted. (Ignored when not
     * ast-scope is used)
     */
    public void setInvert(boolean value) {
        if (invert == value)
            return;
        invert = value;
        notifyChanged();
    }

    private DisplayScope scope;

    /**
     * Specifies the type of expansion that is used on each match.
     */
    public DisplayScope getScope() {
        return scope;
    }

    /**
     * Specifies the type of expansion that is used on each match.
     */
    public void setScope(DisplayScope value) {
        if (scope == value)
            return;
        scope = value;
        notifyChanged();
    }

    private FilterLayout filterLayout;

    /**
     * The {@link FilterLayout} of the current filter.
     */
    public FilterLayout getFilterLayout() {
        return filterLayout;
    }

    /**
     * The {@link FilterLayout} of the current filter.
     */
    public void setFilterLayout(FilterLayout value) {
        if (filterLayout == value)
            return;
        filterLayout = value;
        notifyChanged();
    }

    /**
     * The constructor.
     */
    public PrintFilter() {
        isUserCriteria = true;
        selections = new LinkedList<>();
        before = 2;
        after = 2;
        filterLayout = FilterLayout.Minimize;
        scope = DisplayScope.None;
    }

    /**
     * @return a clone of this object
     */
    public PrintFilter cloneFilter() {
        PrintFilter filter = new PrintFilter();
        filter.setSelections(this.selections);
        filter.setIsUserCriteria(this.isUserCriteria);
        filter.setSearchText(this.searchText);
        filter.setInvert(this.invert);
        filter.setAfter(this.after);
        filter.setBefore(this.before);
        filter.setFilterLayout(this.filterLayout);
        filter.setScope(this.scope);
        return filter;
    }

    private void notifyChanged() {
        this.setChanged();
        this.notifyObservers();
    }

    /**
     * Indicates how lines that did not match any filter should be displayed as
     * (<b>hidden</b>).
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

    /**
     * Indicates how the area that is displayed around a match is extended.
     * 
     * @author Benedikt Gross
     *
     */
    public enum DisplayScope {
        None,

        /**
         * Text lines are used as the unit of expansion. The values
         * <b>before</b> and <b>after</b> are used to extend the visible area
         * around each match.
         */
        Text,

        /**
         * The AST elements are used as the unit of expansion. For each match,
         * the start and end of the line in which the match occurred are check
         * for underlying AST-elements. Each "hit" AST-element is displayed as
         * expansion of the match.
         */
        AST
    }
}
