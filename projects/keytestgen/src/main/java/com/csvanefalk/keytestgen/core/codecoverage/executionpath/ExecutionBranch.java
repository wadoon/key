package com.csvanefalk.keytestgen.core.codecoverage.executionpath;

import de.uka.ilkd.key.java.SourceElement;

public class ExecutionBranch {

    /**
     * The program element which this branch leads to.
     */
    private final SourceElement from;

    /**
     * The program element which this branch leads from.
     */
    private final SourceElement to;

    public ExecutionBranch(final SourceElement first, final SourceElement second) {
        super();
        to = first;
        from = second;
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
