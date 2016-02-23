package de.uka.ilkd.key.nui.prooftree.filter;

import java.util.LinkedList;
import java.util.List;
import java.util.function.Predicate;
import de.uka.ilkd.key.nui.prooftree.NUINode;

public class FilterMultiple implements Predicate<NUINode> {
    
    private List<Predicate<NUINode>> filters = new LinkedList<Predicate<NUINode>>();
    
    @Override
    public boolean test(NUINode node) {
        
        for(Predicate<NUINode> filter : filters) {
            if(filter.test(node))
                return true;
        }
        
        return false;
    }
    
    public void addFilter(Predicate<NUINode> pred) {
        filters.add(pred);
    }
    
    public void setAllFilters(List<Predicate<NUINode>> filters) {
        this.filters = filters;
    }
}
