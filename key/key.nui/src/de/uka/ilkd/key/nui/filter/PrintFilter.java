package de.uka.ilkd.key.nui.filter;

import de.uka.ilkd.key.util.Pair;

public class PrintFilter {

    private String name;

    public String getName() {
        return name;
    }

    public void setName(String value) {
        name = value;
        // no need to notify observer since the name is only for storage
    }


    private String searchText;

    public void setSearchText(String value) {
        searchText = value;
    }

    public String getSearchText() {
        return searchText;
    }

    private Criteria<Pair<Integer, String>> selectionCriteria;

    public void setSelectionCriteria(Criteria<Pair<Integer, String>> value) {
        if (value == selectionCriteria)
            return;
        selectionCriteria = value;
    }

    public Criteria<Pair<Integer, String>> getSelectionCriteria() {
        return selectionCriteria;
    }

    private boolean isUserCriteria;

    public boolean getIsUserCriteria() {
        return isUserCriteria;
    }

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

    public void setInvert(boolean value) {
        invert = value;
    }

    public boolean getInvert() {
        return invert;
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
        return filter;
    }

    public enum FilterLayout {
        Collapse, Minimize
    }
    
    public Criteria<Pair<Integer, String>> createCriteria() {
        Criteria<Pair<Integer, String>> criteria;
        if (this.getIsUserCriteria())
            criteria = new CriterionContainsString(this.getSearchText());
        else
            criteria = this.getSelectionCriteria();

        if (this.getBefore() != 0 || this.getAfter() != 0) {
            criteria = new CriterionRange(this.getBefore(), this.getAfter(),
                    criteria);
        }

        // apply invert as last
        if (this.getInvert())
            criteria = new NotCriteria<>(criteria);

        return criteria;
    }
}
