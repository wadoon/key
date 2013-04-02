package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.TreeMap;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionBranchNode;

import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionBranch;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPath;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPathContext;

public enum BranchCoverageBuilder implements ICoverageBuilder {
    INSTANCE;

    @Override
    public Set<ExecutionPath> retrieveExecutionPaths(
            ExecutionPathContext context) {

        List<ExecutionBranch> executionBranches = context.getExecutionBranches();
        List<ExecutionPath> executionPaths = context.getExecutionPaths();

        /*
         * Create a mapping from which we can deduce which execution path covers
         * which execution branch.
         */
        Map<ExecutionPath, List<ExecutionBranch>> branchesCoveredByPath = new HashMap<ExecutionPath, List<ExecutionBranch>>();
        for (ExecutionBranch executionBranch : executionBranches) {
            List<ExecutionPath> coveringPaths = context.getExecutionPathsForBranch(executionBranch);
            for (ExecutionPath coveringPath : coveringPaths) {
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
        DescendingExecutionBranchComparator descendingExecutionBranchComparator = new DescendingExecutionBranchComparator(
                branchesCoveredByPath);
        PriorityQueue<ExecutionPath> sortedPaths = new PriorityQueue<ExecutionPath>(
                20, descendingExecutionBranchComparator);
        sortedPaths.addAll(executionPaths);

        /*
         * Eliminate from the mapping all those paths which are subsumed by at
         * least one other path in terms of its coverage. The remainder is a
         * minimal set covering all branches.
         */
        while (!sortedPaths.isEmpty()) {
            ExecutionPath targetPath = sortedPaths.poll();
            List<ExecutionBranch> targetBranches = branchesCoveredByPath.get(targetPath);
            for (ExecutionPath otherPath : executionPaths) {
                if (targetPath != otherPath) {
                    List<ExecutionBranch> otherBranches = branchesCoveredByPath.get(otherPath);
                    if (subsumes(targetBranches, otherBranches)) {
                        branchesCoveredByPath.remove(otherPath);
                    }
                }
            }
        }
        
        return branchesCoveredByPath.keySet();
    }

    private boolean subsumes(List<ExecutionBranch> first,
            List<ExecutionBranch> second) {

        if (second.size() > first.size()) {
            return false;
        }

        for (ExecutionBranch branch : second) {
            if (!first.contains(branch)) {
                return false;
            }
        }
        return true;
    }

    private static class DescendingExecutionBranchComparator implements
            Comparator<ExecutionPath> {

        private Map<ExecutionPath, List<ExecutionBranch>> map;

        public DescendingExecutionBranchComparator(
                Map<ExecutionPath, List<ExecutionBranch>> map) {
            this.map = map;
        }

        private int doComparison(ExecutionPath o1, ExecutionPath o2) {
            List<ExecutionBranch> first = map.get(o1);
            List<ExecutionBranch> second = map.get(o2);
            int diff = first.size() - second.size();
            if (diff == 0) {
                return 0;
            } else if (diff > 0) {
                return -1;
            } else {
                return 1;
            }
        }

        @Override
        public int compare(ExecutionPath o1, ExecutionPath o2) {
            return doComparison(o1, o2);
        }
    }
}