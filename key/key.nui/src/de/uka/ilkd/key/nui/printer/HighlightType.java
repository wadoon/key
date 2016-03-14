/**
 *  Use Unique values in incremental order. Value Correspond to
 *  ArrayPosition. Higher Value = Higher Priority.
 */
package de.uka.ilkd.key.nui.printer;

/**
 * @author Maximilian Li
 *
 */
public enum HighlightType {
    MOUSE(0), FILTER(1), SELECTION(2), RULEAPP(3), SEARCH(4), SYNTAX(5);

    private int priority;

    private HighlightType(int i) {
        priority = i;
    }

    public int getPriority() {
        return priority;
    }
}
