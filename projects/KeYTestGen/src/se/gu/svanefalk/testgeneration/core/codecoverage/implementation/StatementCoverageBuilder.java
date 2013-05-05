package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPath;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPathContext;
import de.uka.ilkd.key.java.SourceElement;

public enum StatementCoverageBuilder implements ICoverageBuilder {
    INSTANCE;

    private boolean isSubsetOf(final Set<SourceElement> first,
            final Set<SourceElement> second) {
        if (first.size() > second.size()) {
            return false;
        }

        for (final SourceElement path : first) {
            if (!second.contains(path)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public Set<ExecutionPath> retrieveExecutionPaths(
            final ExecutionPathContext context) {

        final LinkedList<ExecutionPath> originalList = new LinkedList<ExecutionPath>();
        originalList.addAll(context.getExecutionPaths());
        Collections.sort(originalList, ICoverageBuilder.comparator);
        final Set<ExecutionPath> targetSet = new HashSet<ExecutionPath>();
        targetSet.addAll(originalList);

        for (final ExecutionPath firstPath : originalList) {
            for (final ExecutionPath secondPath : originalList) {
                if ((firstPath != secondPath)
                        && subsumes(firstPath, secondPath)) {
                    targetSet.remove(secondPath);
                }
            }
        }
        return targetSet;
    }

    private boolean subsumes(final ExecutionPath firstPath,
            final ExecutionPath secondPath) {
        return isSubsetOf(secondPath.getCoveredNodes(),
                firstPath.getCoveredNodes());
    }
}
