package se.gu.svanefalk.testgeneration.core.codecoverage.executionpath;

import de.uka.ilkd.key.java.SourceElement;

public class ExecutionBranch {

    /**
     * The program element which this branch leads from.
     */
    private final SourceElement to;

    /**
     * The program element which this branch leads to.
     */
    private final SourceElement from;

    public ExecutionBranch(final SourceElement first, final SourceElement second) {
        super();
        this.to = first;
        this.from = second;
    }

    /**
     * @return the to
     */
    public SourceElement getFirst() {
        return to;
    }

    /**
     * @return the from
     */
    public SourceElement getSecond() {
        return from;
    }

    @Override
    public String toString() {
        return to + " --> " + from;
    }
}
