package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.Set;

import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPath;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPathContext;

public interface ICoverageBuilder {

    static DescendingExecutionPathComparator comparator = new DescendingExecutionPathComparator();

    Set<ExecutionPath> retrieveExecutionPaths(ExecutionPathContext context);
}