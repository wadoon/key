package com.csvanefalk.keytestgen.core.codecoverage.implementation;

import com.csvanefalk.keytestgen.core.codecoverage.executionpath.ExecutionPath;
import com.csvanefalk.keytestgen.core.codecoverage.executionpath.ExecutionPathContext;

import java.util.Set;

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
    public Set<ExecutionPath> retrieveExecutionPaths(final ExecutionPathContext context) {
        // TODO Auto-generated method stub
        return null;
    }
}