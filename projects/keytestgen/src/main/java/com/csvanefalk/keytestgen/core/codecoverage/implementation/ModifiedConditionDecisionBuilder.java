package com.csvanefalk.keytestgen.core.codecoverage.implementation;

import com.csvanefalk.keytestgen.core.codecoverage.executionpath.ExecutionPath;
import com.csvanefalk.keytestgen.core.codecoverage.executionpath.ExecutionPathContext;

import java.util.Set;

public class ModifiedConditionDecisionBuilder implements ICoverageBuilder {

    private static ModifiedConditionDecisionBuilder instance = null;

    public static ModifiedConditionDecisionBuilder getInstance() {
        if (ModifiedConditionDecisionBuilder.instance == null) {
            ModifiedConditionDecisionBuilder.instance = new ModifiedConditionDecisionBuilder();
        }
        return ModifiedConditionDecisionBuilder.instance;
    }

    private ModifiedConditionDecisionBuilder() {

    }

    @Override
    public Set<ExecutionPath> retrieveExecutionPaths(final ExecutionPathContext context) {

        return null;
    }
}