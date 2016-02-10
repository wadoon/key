package de.uka.ilkd.key.nui.filter;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.pp.Range;

public class FilterSelection {

    private List<Range> selections = new LinkedList<>();
    public boolean tryAddRange(Range range){
        // if already selected -> deselect
        for (Range r : selections) {
            if (r.start() == range.start() && r.end() == range.end()) {
                selections.remove(r);
                return false;
            }
        }

        selections.add(range);
        return true;
    }
    
    public List<Range> getSelection(){
        return selections;
    }
    
    public Criteria<?> createCriteria(String proofString){
        // get text under ranges
        // add OR to filter
        Range range = null;
        
        proofString.substring(range.start(), range.end());
        return null;
    }
}
