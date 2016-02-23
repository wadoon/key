package de.uka.ilkd.key.nui.prooftree;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.function.Predicate;
import de.uka.ilkd.key.nui.prooftree.filter.FilterMultiple;
import de.uka.ilkd.key.nui.prooftree.filter.HideClosed;
import de.uka.ilkd.key.nui.prooftree.filter.HideIntermediate;
import de.uka.ilkd.key.nui.prooftree.filter.HideNonInteractive;

public class FilteringHandler {
    
    public static final String HIDE_CLOSED = "hideClosed";
    public static final String HIDE_INTERMEDIATE = "hideIntermediate";
    public static final String HIDE_NON_INTERACTIVE = "hideNonInteractive";
    HashMap<String, Predicate<NUINode>> filters = new HashMap<String, Predicate<NUINode>>();
    
    public FilteringHandler() {
        
    }
    
    public void refreshFilters() {
        Predicate<NUINode> theFilter;
        ArrayList<Predicate<NUINode>> list = new ArrayList<Predicate<NUINode>>(filters.values());
        
        if(!list.isEmpty()) {
            if(list.size() == 1) {
                theFilter = list.get(0);
            }
            else {
                FilterMultiple andFilter = new FilterMultiple();
                andFilter.setAllFilters(list);
                
                theFilter = andFilter;
            }
        }
        
        //TODO apply filter...
    }
    
    public void toggleFilterHideClosed() {
        System.out.println("TOGGGGLE NOW");
        
        if(filters.containsKey(HIDE_CLOSED)) {
            filters.remove(HIDE_CLOSED);
        } else {
            filters.put(HIDE_CLOSED, new HideClosed());
        }
        
        refreshFilters();
        //printF();
    }
    
    public void toggleFilterHideIntermediate() {
        if(filters.containsKey(HIDE_INTERMEDIATE)) {
            filters.remove(HIDE_INTERMEDIATE);
        } else {
            filters.put(HIDE_INTERMEDIATE, new HideIntermediate());
        }
        
        refreshFilters();
    }
    
    public void toggleFilterHideNonInteractive() {
        if(filters.containsKey(HIDE_NON_INTERACTIVE)) {
            filters.remove(HIDE_NON_INTERACTIVE);
        } else {
            filters.put(HIDE_NON_INTERACTIVE, new HideNonInteractive());
        }
        
        refreshFilters();
    }

    
    public void printF() {
        System.out.println(getFilterStatus(HIDE_NON_INTERACTIVE) + 
                "|" + getFilterStatus(HIDE_INTERMEDIATE) +
                "|" + getFilterStatus(HIDE_CLOSED));
    }
    
    public boolean getFilterStatus(String filterKey) {
        return filters.containsKey(filterKey);
    }
}