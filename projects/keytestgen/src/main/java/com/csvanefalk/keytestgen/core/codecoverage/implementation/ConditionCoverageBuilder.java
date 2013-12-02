package com.csvanefalk.keytestgen.core.codecoverage.implementation;

import com.csvanefalk.keytestgen.core.codecoverage.executionpath.ExecutionPath;
import com.csvanefalk.keytestgen.core.codecoverage.executionpath.ExecutionPathContext;

import java.util.Set;

public class ConditionCoverageBuilder implements ICoverageBuilder {

    private static ConditionCoverageBuilder instance = null;

    public static ConditionCoverageBuilder getInstance() {
        if (ConditionCoverageBuilder.instance == null) {
            ConditionCoverageBuilder.instance = new ConditionCoverageBuilder();
        }
        return ConditionCoverageBuilder.instance;
    }

    private ConditionCoverageBuilder() {

    }

    @Override
    public Set<ExecutionPath> retrieveExecutionPaths(
            final ExecutionPathContext context) {

        return null;
    }
}