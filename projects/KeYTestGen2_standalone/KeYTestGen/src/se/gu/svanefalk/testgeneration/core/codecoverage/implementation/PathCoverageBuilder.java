package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.Set;

import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPath;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPathContext;

public class PathCoverageBuilder implements ICoverageBuilder {

    private static PathCoverageBuilder instance = null;

    public static PathCoverageBuilder getInstance() {
        if (PathCoverageBuilder.instance == null) {
            PathCoverageBuilder.instance = new PathCoverageBuilder();
        }
        return PathCoverageBuilder.instance;
    }

    private PathCoverageBuilder() {

    }

    @Override
    public Set<ExecutionPath> retrieveExecutionPaths(
            final ExecutionPathContext context) {
        // TODO Auto-generated method stub
        return null;
    }
}