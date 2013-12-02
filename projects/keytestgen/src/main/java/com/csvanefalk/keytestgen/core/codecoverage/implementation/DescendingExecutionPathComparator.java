package com.csvanefalk.keytestgen.core.codecoverage.implementation;

import com.csvanefalk.keytestgen.core.codecoverage.executionpath.ExecutionPath;

import java.util.Comparator;

public class DescendingExecutionPathComparator implements
        Comparator<ExecutionPath> {

    @Override
    public int compare(final ExecutionPath o1, final ExecutionPath o2) {
        final int diff = o1.getCoveredNodes().size()
                - o2.getCoveredNodes().size();

        if (diff == 0) {
            return 0;
        } else if (diff > 0) {
            return -1;
        } else {
            return 1;
        }
    }
}
