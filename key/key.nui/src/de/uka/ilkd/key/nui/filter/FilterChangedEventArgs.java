package de.uka.ilkd.key.nui.filter;

import de.uka.ilkd.key.nui.filter.PrintFilter.FilterLayout;
import de.uka.ilkd.key.util.Pair;

public class FilterChangedEventArgs {

    private Criteria<Pair<Integer, String>> criteria;
    private FilterLayout layout;

    public FilterChangedEventArgs(FilterLayout layout,
            Criteria<Pair<Integer, String>> criteria) {
        this.layout = layout;
        this.criteria = criteria;
    }
    
    public Criteria<Pair<Integer,String>> getCriteria(){
        return criteria;
    }

    public FilterLayout getLayout(){
        return layout;
    }
}
