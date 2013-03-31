package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.Comparator;

import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPath;

public class DescendingExecutionPathComparator implements
        Comparator<ExecutionPath> {

    @Override
    public int compare(ExecutionPath o1, ExecutionPath o2) {
        int diff = o1.getCoveredNodes().size() - o2.getCoveredNodes().size();

        if (diff == 0) {
            return 0;
        } else if (diff > 0) {
            return -1;
        } else {
            return 1;
        }
    }
}
