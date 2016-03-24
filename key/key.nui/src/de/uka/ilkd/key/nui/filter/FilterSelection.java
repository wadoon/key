package de.uka.ilkd.key.nui.filter;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.nui.event.EmptyEventArgs;
import de.uka.ilkd.key.nui.event.HandlerEvent;
import de.uka.ilkd.key.pp.Range;

/**
 * This class provides all information and logic for one triggered filter
 * selection operation.
 * 
 * @author Benedikt Gross
 * @version 1.0
 */
public class FilterSelection {

    private List<Range> selections = new LinkedList<>();

    public FilterSelection() {

    }

    /**
     * Add a range to the selection, if it was not already selected.
     * 
     * @param range
     * @return
     */
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

    /**
     * 
     * @return all selections
     */
    public List<Range> getSelection() {
        return selections;
    }

    /**
     * Creates a criterion that represents all selections combined by
     * {@link OrCriterion} and saves it in this instance. The created criterion
     * can be accessed via getCriteria().
     * 
     * @param proofString
     */
    public void resolveSelection(String proofString) {
        // get text under ranges
        List<String> list = new LinkedList<>();

        for (Range range : selections) {
            String searchString = proofString.substring(range.start(),
                    range.end());
            list.add(searchString);
        }
        this.resolvedSelection = list;
    }

    private List<String> resolvedSelection;

    /**
     * Returns the criterion created by a previous call to createCriteria(). If
     * createCriteria was not called before null is returned.
     * 
     * @return
     */
    public List<String> getResolvedSelection() {
        return resolvedSelection;
    }

    private HandlerEvent<EmptyEventArgs> selectionModeFinishedEvent = new HandlerEvent<>();

    /**
     * @return An event that is raised if the user aborts or closes the selection
     * "mode".
     */
    public HandlerEvent<EmptyEventArgs> getSelectionModeFinishedEvent() {
        return selectionModeFinishedEvent;
    }
}
