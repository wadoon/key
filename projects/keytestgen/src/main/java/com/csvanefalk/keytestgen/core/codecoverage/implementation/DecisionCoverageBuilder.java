package com.csvanefalk.keytestgen.core.codecoverage.implementation;

import com.csvanefalk.keytestgen.core.codecoverage.executionpath.ExecutionPath;
import com.csvanefalk.keytestgen.core.codecoverage.executionpath.ExecutionPathContext;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.java.statement.If;
import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.util.*;

public class DecisionCoverageBuilder implements ICoverageBuilder {

    private static class DescendingExecutionBranchComparator implements Comparator<ExecutionPath> {

        private final Map<ExecutionPath, Set<BranchStatement>> map;

        public DescendingExecutionBranchComparator(final Map<ExecutionPath, Set<BranchStatement>> map) {
            this.map = map;
        }

        @Override
        public int compare(final ExecutionPath o1, final ExecutionPath o2) {
            return doComparison(o1, o2);
        }

        private int doComparison(final ExecutionPath o1, final ExecutionPath o2) {
            final Set<BranchStatement> first = map.get(o1);
            final Set<BranchStatement> second = map.get(o2);

            if ((first == null) && (second == null)) {
                return 0;
            } else if ((first == null) && (second != null)) {
                return -1;
            } else if ((first != null) && (second == null)) {
                return 1;
            }

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

    private static DecisionCoverageBuilder instance = null;

    public static DecisionCoverageBuilder getInstance() {
        if (DecisionCoverageBuilder.instance == null) {
            DecisionCoverageBuilder.instance = new DecisionCoverageBuilder();
        }
        return DecisionCoverageBuilder.instance;
    }

    private DecisionCoverageBuilder() {

    }

    /**
     * From a set of {@link SourceElement} instances, extracts all instances of
     * {@link BranchStatement} as a separate subset.
     *
     * @param visitedProgramNodes
     * @return
     */
    private Set<BranchStatement> collectBranchStatements(final Set<SourceElement> visitedProgramNodes) {

        final Set<BranchStatement> branchStatements = new HashSet<BranchStatement>();
        for (final SourceElement element : visitedProgramNodes) {
            if (element instanceof BranchStatement) {
                branchStatements.add((BranchStatement) element);
            }
        }
        return branchStatements;
    }

    private Set<ExecutionPath> constructMinimalSetForMapping(final PriorityQueue<ExecutionPath> sortedPaths,
                                                             final Map<ExecutionPath, Set<BranchStatement>> mapping) {

        while (!sortedPaths.isEmpty()) {
            final ExecutionPath executionPath = sortedPaths.poll();
            final Set<BranchStatement> branchStatements = mapping.get(executionPath);
            if (branchStatements != null) {
                for (final ExecutionPath pathToCompare : sortedPaths) {
                    final Set<BranchStatement> branchStatementsToCompare = mapping.get(pathToCompare);
                    if (branchStatementsToCompare != null) {
                        if (subsumes(branchStatements, branchStatementsToCompare)) {
                            mapping.remove(pathToCompare);
                        }
                    }
                }
            }
        }

        final Set<ExecutionPath> minimalSet = new HashSet<ExecutionPath>();
        for (final ExecutionPath path : mapping.keySet()) {
            minimalSet.add(path);
        }
        return minimalSet;
    }

    private boolean contains(final ExecutionPath path, final SourceElement branchResult) {

        if (branchResult == null) {
            return false;
        }

        for (final SourceElement element : path.getCoveredNodes()) {
            if (element == branchResult) {
                return true;
            }
        }
        return false;
    }

    /**
     * Retrieves the {@link SourceElement} reached from a given branch of a
     * {@link BranchStatement}.
     *
     * @param thenBranchResult
     * @return
     */
    private SourceElement getStatementOnBranch(final SourceElement thenBranchResult) {
        if (thenBranchResult instanceof StatementBlock) {
            return ((StatementBlock) thenBranchResult).getChildAt(0);
        } else {
            return thenBranchResult;
        }
    }

    @Override
    public Set<ExecutionPath> retrieveExecutionPaths(final ExecutionPathContext context) {

        /*
         * Create two separate mappings - one which maps, for each execution
         * branch, the branching nodes in which the Then branch is taken by that
         * path. Conversely, do the same for the Else branch.
         */
        final Set<BranchStatement> branchStatements = collectBranchStatements(context.getVisitedProgramNodes());
        final List<ExecutionPath> executionPaths = context.getExecutionPaths();

        final Map<ExecutionPath, Set<BranchStatement>> thenMapping = new HashMap<ExecutionPath, Set<BranchStatement>>();
        final Map<ExecutionPath, Set<BranchStatement>> elseMapping = new HashMap<ExecutionPath, Set<BranchStatement>>();

        for (final BranchStatement branchStatement : branchStatements) {
            if (branchStatement instanceof If) {

                final If ifBranch = (If) branchStatement;

                SourceElement thenBranchResult = null;
                SourceElement elseBranchResult = null;

                /*
                 * One or both of the outcomes of the If-statement may be
                 * fall-throughs, and we need to deal with them accordingly.
                 */
                if (ifBranch.getThen() != null) {
                    thenBranchResult = ifBranch.getThen().getBody();
                    thenBranchResult = getStatementOnBranch(thenBranchResult);
                }
                if (ifBranch.getElse() != null) {
                    elseBranchResult = ifBranch.getElse().getBody();
                    elseBranchResult = getStatementOnBranch(elseBranchResult);
                }

                /*
                 * FIXME: ALGORITHM IS BROKEN: does not handle cases where BOTH
                 * outcomes are fall-throughs...not that any serious programmer
                 * should ever write code like that, but still.
                 */
                for (final ExecutionPath path : executionPaths) {
                    if (contains(path, ifBranch)) {
                        if (contains(path, thenBranchResult)) {
                            Set<BranchStatement> mappedElements = thenMapping.get(path);
                            if (mappedElements == null) {
                                mappedElements = new HashSet<BranchStatement>();
                                thenMapping.put(path, mappedElements);
                            }
                            mappedElements.add(branchStatement);

                        } else {
                            Set<BranchStatement> mappedElements = elseMapping.get(path);
                            if (mappedElements == null) {
                                mappedElements = new HashSet<BranchStatement>();
                                elseMapping.put(path, mappedElements);
                            }
                            mappedElements.add(branchStatement);
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
        final PriorityQueue<ExecutionPath> thenSortedPaths = new PriorityQueue<ExecutionPath>(20,
                                                                                              new DescendingExecutionBranchComparator(
                                                                                                      thenMapping));
        final PriorityQueue<ExecutionPath> elseSortedPaths = new PriorityQueue<ExecutionPath>(20,
                                                                                              new DescendingExecutionBranchComparator(
                                                                                                      elseMapping));

        for (final ExecutionPath executionPath : executionPaths) {
            thenSortedPaths.add(executionPath);
            elseSortedPaths.add(executionPath);
        }

        /*
         * Construct minimum set for the both mappings
         */
        final Set<ExecutionPath> minimalThenPaths = constructMinimalSetForMapping(thenSortedPaths, thenMapping);
        final Set<ExecutionPath> minimalElsePaths = constructMinimalSetForMapping(elseSortedPaths, elseMapping);

        /*
         * Return the union of the sets.
         */
        minimalThenPaths.addAll(minimalElsePaths);
        return minimalThenPaths;
    }

    private boolean subsumes(final Set<BranchStatement> first, final Set<BranchStatement> second) {

        if (second.size() > first.size()) {
            return false;
        }

        for (final BranchStatement branchStatement : second) {
            if (!first.contains(branchStatement)) {
                return false;
            }
        }
        return true;
    }
}
