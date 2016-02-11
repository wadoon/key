package de.uka.ilkd.key.nui.filter;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.nui.util.CsEvent;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.util.Pair;

public class FilterSelection {

    private List<Range> selections = new LinkedList<>();

    public FilterSelection(){
        
    }
    
    public boolean tryAddRange(Range range) {
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

    public List<Range> getSelection() {
        return selections;
    }

    public void createCriteria(String proofString) {
        // get text under ranges
        // add OR to filter
        Criteria<Pair<Integer, String>> criteria = null;
        boolean first = true;

        for (Range range : selections) {
            String searchString = proofString.substring(range.start(),
                    range.end());
            if (first) {
                criteria = new CriterionContainsString(searchString);
                first = false;
            }
            else {
                criteria = new OrCriteria<>(criteria,
                        new CriterionContainsString(searchString));
            }
        }

        this.criteria = criteria;
    }

    private Criteria<Pair<Integer, String>> criteria = null;

    public Criteria<Pair<Integer, String>> getCriteria() {
        return criteria;
    }

    private CsEvent<EmptyEventArgs> selectionModeFinishedEvent = new CsEvent<>();

    public CsEvent<EmptyEventArgs> getSelectionModeFinishedEvent() {
        return selectionModeFinishedEvent;
    }
}
