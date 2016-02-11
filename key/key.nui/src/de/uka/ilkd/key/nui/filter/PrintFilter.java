package de.uka.ilkd.key.nui.filter;

import java.util.List;
import java.util.Objects;
import java.util.Observable;

import javax.lang.model.element.Parameterizable;

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

    private Criteria<Pair<Integer, String>> criteria;

    public void setCriteria(Criteria<Pair<Integer, String>> value) {
        if (value == criteria)
            return;
        criteria = value;
    }

    public Criteria<Pair<Integer, String>> getCriteria() {
        return criteria;
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
        criteria = new CriterionEmpty<Pair<Integer,String>>();
        before = 2;
        after = 2;
        filterLayout = FilterLayout.Minimize;
    }

    public PrintFilter cloneFilter() {
        PrintFilter filter = new PrintFilter();
        filter.setName(this.name);
        filter.setCriteria(this.criteria);
        filter.setIsUserCriteria(this.isUserCriteria);
        filter.setAfter(this.after);
        filter.setBefore(this.before);
        filter.setFilterLayout(this.filterLayout);
        return filter;
    }

    public enum FilterLayout {
        Collapse, Minimize
    }
}
