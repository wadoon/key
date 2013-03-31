package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.Set;

import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPath;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPathContext;

public enum BranchCoverageBuilder implements ICoverageBuilder {
    INSTANCE;

    @Override
    public Set<ExecutionPath> retrieveExecutionPaths(
            ExecutionPathContext context) {

        return null;
    }
}