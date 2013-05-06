package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.Set;

import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPath;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPathContext;

public class ModifiedConditionDecisionBuilder implements ICoverageBuilder {
    
    private static ModifiedConditionDecisionBuilder instance = null;

    public static ModifiedConditionDecisionBuilder getInstance() {
        if (instance == null) {
            instance = new ModifiedConditionDecisionBuilder();
        }
        return instance;
    }
    
    private ModifiedConditionDecisionBuilder() {
        
    }

    @Override
    public Set<ExecutionPath> retrieveExecutionPaths(
            final ExecutionPathContext context) {

        return null;
    }
}