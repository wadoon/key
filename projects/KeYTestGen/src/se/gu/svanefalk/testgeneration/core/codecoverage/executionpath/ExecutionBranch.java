package se.gu.svanefalk.testgeneration.core.codecoverage.executionpath;

import de.uka.ilkd.key.java.SourceElement;

public class ExecutionBranch {

    private final SourceElement first;

    private final SourceElement second;

    public ExecutionBranch(final SourceElement first, final SourceElement second) {
        super();
        this.first = first;
        this.second = second;
    }

    /**
     * @return the first
     */
    public SourceElement getFirst() {
        return this.first;
    }

    /**
     * @return the second
     */
    public SourceElement getSecond() {
        return this.second;
    }

    @Override
    public String toString() {
        // TODO Auto-generated method stub
        return this.first + " --> " + this.second;
    }
}
