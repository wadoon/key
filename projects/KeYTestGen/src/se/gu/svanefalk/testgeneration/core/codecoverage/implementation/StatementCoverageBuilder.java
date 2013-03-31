package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPath;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPathContext;
import de.uka.ilkd.key.java.SourceElement;

public enum StatementCoverageBuilder implements ICoverageBuilder {
    INSTANCE;

    @Override
    public Set<ExecutionPath> retrieveExecutionPaths(
            ExecutionPathContext context) {

        LinkedList<ExecutionPath> originalList = new LinkedList<ExecutionPath>();
        originalList.addAll(context.getExecutionPaths());
        Collections.sort(originalList, comparator);
        Set<ExecutionPath> targetSet = new HashSet<ExecutionPath>();
        targetSet.addAll(originalList);

        for (ExecutionPath firstPath : originalList) {
            for (ExecutionPath secondPath : originalList) {
                if (firstPath != secondPath && subsumes(firstPath, secondPath)) {
                    targetSet.remove(secondPath);
                }
            }
        }
        return targetSet;
    }

    private boolean subsumes(ExecutionPath firstPath, ExecutionPath secondPath) {
        return isSubsetOf(secondPath.getCoveredNodes(),
                firstPath.getCoveredNodes());
    }

    private boolean isSubsetOf(Set<SourceElement> first,
            Set<SourceElement> second) {
        if (first.size() > second.size()) {
            return false;
        }

        for (SourceElement path : first) {
            if (!second.contains(path)) {
                return false;
            }
        }
        return true;
    }

    private static class DescendingPathComparator implements
            Comparator<ExecutionPath> {

        @Override
        public int compare(ExecutionPath o1, ExecutionPath o2) {
            int diff = o1.getCoveredNodes().size()
                    - o2.getCoveredNodes().size();

            if (diff == 0) {
                return 0;
            } else if (diff > 0) {
                return -1;
            } else {
                return 1;
            }
        }
    }
}
