package se.gu.svanefalk.testgeneration.core.codecoverage.executionpath;

import de.uka.ilkd.key.java.SourceElement;

public class ExecutionBranch {

    public ExecutionBranch(SourceElement first, SourceElement second) {
        super();
        this.first = first;
        this.second = second;
    }

    private final SourceElement first;
    private final SourceElement second;

    @Override
    public String toString() {
        // TODO Auto-generated method stub
        return first + " --> " + second;
    }

    /**
     * @return the first
     */
    public SourceElement getFirst() {
        return first;
    }

    /**
     * @return the second
     */
    public SourceElement getSecond() {
        return second;
    }
}
