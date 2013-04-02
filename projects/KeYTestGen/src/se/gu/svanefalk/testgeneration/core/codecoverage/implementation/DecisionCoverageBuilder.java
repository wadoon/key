package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;

import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPath;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPathContext;
import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.java.statement.If;

public enum DecisionCoverageBuilder implements ICoverageBuilder {
    INSTANCE;

    @Override
    public Set<ExecutionPath> retrieveExecutionPaths(
            ExecutionPathContext context) {

        /*
         * Create two separate mappings - one which maps, for each execution
         * branch, the branching nodes in which the Then branch is taken by that
         * path. Conversely, do the same for the Else branch.
         */
        Set<BranchStatement> branchStatements = collectBranchStatements(context.getVisitedProgramNodes());
        List<ExecutionPath> executionPaths = context.getExecutionPaths();

        Map<ExecutionPath, Set<BranchStatement>> thenMapping = new HashMap<ExecutionPath, Set<BranchStatement>>();
        Map<ExecutionPath, Set<BranchStatement>> elseMapping = new HashMap<ExecutionPath, Set<BranchStatement>>();

        for (BranchStatement branchStatement : branchStatements) {
            if (branchStatement instanceof If) {
                If ifBranch = (If) branchStatement;
                SourceElement thenBranchResult = ifBranch.getThen().getBody();
                SourceElement elseBranchResult = ifBranch.getElse().getBody();

                for (ExecutionPath path : executionPaths) {
                    if (contains(path, thenBranchResult)) {
                        Set<BranchStatement> mappedElements = thenMapping.get(path);
                        if (mappedElements == null) {
                            mappedElements = new HashSet<BranchStatement>();
                            thenMapping.put(path, mappedElements);
                        }
                        mappedElements.add(branchStatement);
                    } else if (contains(path, elseBranchResult)) {
                        Set<BranchStatement> mappedElements = elseMapping.get(path);
                        if (mappedElements == null) {
                            mappedElements = new HashSet<BranchStatement>();
                            thenMapping.put(path, mappedElements);
                        }
                    }
                }
            } else {
                throw new NotImplementedException();
            }
        }

        /*
         * For both mappings, create a minimal set of paths which cover all
         * branching nodes, and then create the final set by taking the union of
         * these two sets. This is most likely NOT an optimal algorithm for
         * calculating a minimal set.
         */
        PriorityQueue<ExecutionPath> thenSortedPaths = new PriorityQueue<>(20,
                new DescendingExecutionBranchComparator(thenMapping));
        PriorityQueue<ExecutionPath> elseSortedPaths = new PriorityQueue<>(20,
                new DescendingExecutionBranchComparator(elseMapping));

        for (ExecutionPath executionPath : executionPaths) {
            thenSortedPaths.add(executionPath);
            elseSortedPaths.add(executionPath);
        }

        /*
         * Construct minimum set for the both mappings
         */
        Set<ExecutionPath> minimalThenPaths = constructMinimalSetForMapping(
                thenSortedPaths, thenMapping);
        Set<ExecutionPath> minimalElsePaths = constructMinimalSetForMapping(
                elseSortedPaths, elseMapping);

        /*
         * Return the union of the sets.
         */
        minimalThenPaths.addAll(minimalElsePaths);
        return minimalThenPaths;
    }

    private Set<ExecutionPath> constructMinimalSetForMapping(
            PriorityQueue<ExecutionPath> sortedPaths,
            Map<ExecutionPath, Set<BranchStatement>> mapping) {

        while (!sortedPaths.isEmpty()) {
            ExecutionPath executionPath = sortedPaths.poll();
            Set<BranchStatement> branchStatements = mapping.get(executionPath);
            for (ExecutionPath pathToCompare : sortedPaths) {
                Set<BranchStatement> branchStatementsToCompare = mapping.get(pathToCompare);
                if (branchStatementsToCompare != null) {
                    if (subsumes(branchStatements, branchStatementsToCompare)) {
                        mapping.remove(pathToCompare);
                    }
                }
            }
        }

        Set<ExecutionPath> minimalSet = new HashSet<>();
        for (ExecutionPath path : mapping.keySet()) {
            minimalSet.add(path);
        }
        return minimalSet;
    }

    private boolean contains(ExecutionPath path, SourceElement thenBranchResult) {

        for (SourceElement element : path.getCoveredNodes()) {
            if (element == thenBranchResult) {
                return true;
            }
        }
        return false;
    }

    private Set<BranchStatement> collectBranchStatements(
            Set<SourceElement> visitedProgramNodes) {

        Set<BranchStatement> branchStatements = new HashSet<>();
        for (SourceElement element : visitedProgramNodes) {
            if (element instanceof BranchStatement) {
                branchStatements.add((BranchStatement) element);
            }
        }
        return branchStatements;
    }

    private static class DescendingExecutionBranchComparator implements
            Comparator<ExecutionPath> {

        private Map<ExecutionPath, Set<BranchStatement>> map;

        public DescendingExecutionBranchComparator(
                Map<ExecutionPath, Set<BranchStatement>> map) {
            this.map = map;
        }

        private int doComparison(ExecutionPath o1, ExecutionPath o2) {
            Set<BranchStatement> first = map.get(o1);
            Set<BranchStatement> second = map.get(o2);
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

    private boolean subsumes(Set<BranchStatement> first,
            Set<BranchStatement> second) {

        if (second.size() > first.size()) {
            return false;
        }

        for (BranchStatement branchStatement : second) {
            if (!first.contains(branchStatement)) {
                return false;
            }
        }
        return true;
    }
}
