package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPath;
import se.gu.svanefalk.testgeneration.core.codecoverage.executionpath.ExecutionPathContext;
import de.uka.ilkd.key.java.SourceElement;

/**
 * Extracts the execution paths needed in order to provide Statement Coverage.
 * 
 * @author christopher
 * 
 */
public class StatementCoverageBuilder implements ICoverageBuilder {

    /**
     * Singleton instance of this class.
     */
    private static StatementCoverageBuilder instance = null;

    /**
     * Gets a singleton instance for this class.
     * 
     * @return the instance
     */
    public static StatementCoverageBuilder getInstance() {
        if (StatementCoverageBuilder.instance == null) {
            StatementCoverageBuilder.instance = new StatementCoverageBuilder();
        }
        return StatementCoverageBuilder.instance;
    }

    /**
     * Constructor locked - this class is a singleton.
     */
    private StatementCoverageBuilder() {

    }

    /**
     * @param first
     *            the first set
     * @param second
     *            the second set
     * @return true if the first set is a subset of the second, false otherwise.
     */
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

        /*
         * Create a list of the execution paths existing prior to the execution
         * of the body of the algorithm.
         */
        final LinkedList<ExecutionPath> originalList = new LinkedList<ExecutionPath>();
        originalList.addAll(context.getExecutionPaths());

        /*
         * Sort the list of paths according to the number of nodes covered by
         * each.
         */
        Collections.sort(originalList, ICoverageBuilder.comparator);

        final Set<ExecutionPath> targetSet = new HashSet<ExecutionPath>();
        targetSet.addAll(originalList);

        /*
         * Main loop - go through all the sorted paths, and remove the ones
         * which are subsumed by another path. The resulting set is a minimal
         * set of paths giving statement coverage.
         */
        for (final ExecutionPath firstPath : originalList) {

            /*
             * Work around the fact that the model is modified during
             * iterations.
             */
            if (targetSet.contains(firstPath)) {
                for (final ExecutionPath secondPath : originalList) {
                    if ((firstPath != secondPath)
                            && subsumes(firstPath, secondPath)) {
                        targetSet.remove(secondPath);
                    }
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
