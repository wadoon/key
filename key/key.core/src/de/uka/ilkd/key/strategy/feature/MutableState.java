package de.uka.ilkd.key.strategy.feature;

import java.util.HashMap;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.instantiator.BackTrackingManager;
import de.uka.ilkd.key.strategy.feature.instantiator.ChoicePoint;
import de.uka.ilkd.key.strategy.termProjection.TermBuffer;

/**
 * Realizes a variable bank for strategy features such that each feature
 * computation can be done in parallel.
 *
 * When the strategy computes the costs for a {@link RuleApp} it creates
 * a new MutableState object and passes it on. This is then used by features
 * to query for the value of {@link TermBuffer}s.
 *
 * This mutable state should not be abused and strategy features should be stateless.
 *
 *
 * @author Richard Bubel
 */
public class MutableState {

    /** maps a term buffer to its value */
    private HashMap<TermBuffer, Term> content;

    /** manages backtracking for features that create {@link ChoicePoint}s */
    private BackTrackingManager btManager;

    /**
     * assign the given {@link TermBuffer} the provided value
     * @param v the {@link TermBuffer}
     * @param value the Term which is assigned as the value
     */
    public void assign(TermBuffer v, Term value) {
        if (content == null) {
            content = new HashMap<>();
        }
        content.put(v, value);
    }

    /**
     * retrieves the current value of the given {@link TermBuffer}
     * @param v the TermBuffer whose value is asked for
     * @return the current value of the {@link TermBuffer} or {@code null} if there is none
     */
    public Term read(TermBuffer v) {
        if (content == null) {
            return null;
        }
        return content.get(v);
    }

    /**
     * returns the backtracking manager to access {@link ChoicePoint}s
     * @return the backtracking manager
     */
    public BackTrackingManager getBacktrackingManager() {
        if (btManager == null) {
            btManager = new BackTrackingManager();
        }
        return btManager;
    }
}
