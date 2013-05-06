package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.Set;

import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPath;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPathContext;

public class ConditionCoverageBuilder implements ICoverageBuilder {
    
    private static ConditionCoverageBuilder instance = null;

    public static ConditionCoverageBuilder getInstance() {
        if (instance == null) {
            instance = new ConditionCoverageBuilder();
        }
        return instance;
    }
    
    private ConditionCoverageBuilder() {
        
    }


    @Override
    public Set<ExecutionPath> retrieveExecutionPaths(
            final ExecutionPathContext context) {

        return null;
    }
}