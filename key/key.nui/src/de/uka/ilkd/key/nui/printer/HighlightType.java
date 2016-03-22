package de.uka.ilkd.key.nui.printer;

/**
 * Use Unique values in incremental order. Value Correspond to ArrayPosition.
 * Higher Value = Higher Priority.
 * 
 * @author Maximilian Li
 * @version 1.0
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
