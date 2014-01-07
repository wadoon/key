package com.csvanefalk.keytestgen.core.codecoverage.implementation;

import com.csvanefalk.keytestgen.core.codecoverage.executionpath.ExecutionPath;
import com.csvanefalk.keytestgen.core.codecoverage.executionpath.ExecutionPathContext;

import java.util.Set;

public interface ICoverageBuilder {

    static DescendingExecutionPathComparator comparator = new DescendingExecutionPathComparator();

    Set<ExecutionPath> retrieveExecutionPaths(ExecutionPathContext context);
}