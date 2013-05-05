package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;

import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionBranch;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPath;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPathContext;

public enum BranchCoverageBuilder implements ICoverageBuilder {
    INSTANCE;

    private static class DescendingExecutionBranchComparator implements
            Comparator<ExecutionPath> {

        private final Map<ExecutionPath, List<ExecutionBranch>> map;

        public DescendingExecutionBranchComparator(
                final Map<ExecutionPath, List<ExecutionBranch>> map) {
            this.map = map;
        }

        @Override
        public int compare(final ExecutionPath o1, final ExecutionPath o2) {
            return doComparison(o1, o2);
        }

        private int doComparison(final ExecutionPath o1, final ExecutionPath o2) {
            final List<ExecutionBranch> first = map.get(o1);
            final List<ExecutionBranch> second = map.get(o2);
            final int diff = first.size() - second.size();
            if (diff == 0) {
                return 0;
            } else if (diff > 0) {
                return -1;
            } else {
                return 1;
            }
        }
    }

    @Override
    public Set<ExecutionPath> retrieveExecutionPaths(
            final ExecutionPathContext context) {

        final List<ExecutionBranch> executionBranches = context.getExecutionBranches();
        final List<ExecutionPath> executionPaths = context.getExecutionPaths();

        /*
         * Create a mapping from which we can deduce which execution path covers
         * which execution branch.
         */
        final Map<ExecutionPath, List<ExecutionBranch>> branchesCoveredByPath = new HashMap<ExecutionPath, List<ExecutionBranch>>();
        for (final ExecutionBranch executionBranch : executionBranches) {
            final List<ExecutionPath> coveringPaths = context.getExecutionPathsForBranch(executionBranch);
            for (final ExecutionPath coveringPath : coveringPaths) {
                List<ExecutionBranch> coveredBranches = branchesCoveredByPath.get(coveringPath);
                if (coveredBranches == null) {
                    coveredBranches = new LinkedList<ExecutionBranch>();
                    branchesCoveredByPath.put(coveringPath, coveredBranches);
                }
                coveredBranches.add(executionBranch);
            }
        }

        /*
         * Sort the mapping
         */
        final DescendingExecutionBranchComparator descendingExecutionBranchComparator = new DescendingExecutionBranchComparator(
                branchesCoveredByPath);
        final PriorityQueue<ExecutionPath> sortedPaths = new PriorityQueue<ExecutionPath>(
                20, descendingExecutionBranchComparator);
        sortedPaths.addAll(executionPaths);

        /*
         * Eliminate from the mapping all those paths which are subsumed by at
         * least one other path in terms of its coverage. The remainder is a
         * minimal set covering all branches.
         */
        while (!sortedPaths.isEmpty()) {
            final ExecutionPath targetPath = sortedPaths.poll();
            final List<ExecutionBranch> targetBranches = branchesCoveredByPath.get(targetPath);
            for (final ExecutionPath otherPath : executionPaths) {
                if (targetPath != otherPath) {
                    final List<ExecutionBranch> otherBranches = branchesCoveredByPath.get(otherPath);
                    if (subsumes(targetBranches, otherBranches)) {
                        branchesCoveredByPath.remove(otherPath);
                    }
                }
            }
        }

        return branchesCoveredByPath.keySet();
    }

    private boolean subsumes(final List<ExecutionBranch> first,
            final List<ExecutionBranch> second) {

        if (second.size() > first.size()) {
            return false;
        }

        for (final ExecutionBranch branch : second) {
            if (!first.contains(branch)) {
                return false;
            }
        }
        return true;
    }
}