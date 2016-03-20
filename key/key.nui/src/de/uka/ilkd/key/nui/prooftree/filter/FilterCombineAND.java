package de.uka.ilkd.key.nui.prooftree.filter;

import de.uka.ilkd.key.nui.prooftree.NUINode;

/**
 * A filter that can be used to combine two filters via AND.
 * 
 * @author Matthias Schultheis
 *
 */
public class FilterCombineAND implements ProofTreeFilter {

    /**
     * The first filter used for combination.
     */

    private final ProofTreeFilter filter1;
    /**
     * The second filter used for combination.
     */
    private final ProofTreeFilter filter2;

    /**
     * Constructor.
     * 
     * @param filter1
     *            The first filter.
     * @param filter2
     *            The second filter.
     */

    public FilterCombineAND(final ProofTreeFilter filter1, final ProofTreeFilter filter2) {
        this.filter1 = filter1;
        this.filter2 = filter2;

    }

    @Override
    public String getContextMenuItemText() {
        return "";
    }

    /**
     * TODO
     * 
     * @return
     */
    public ProofTreeFilter getFilter1() {
        return filter1;
    }

    /**
     * TODO
     * 
     * @return
     */
    public ProofTreeFilter getFilter2() {
        return filter2;
    }

    @Override
    public boolean test(final NUINode node) {
        return filter1.test(node) && filter2.test(node);
    }
}
