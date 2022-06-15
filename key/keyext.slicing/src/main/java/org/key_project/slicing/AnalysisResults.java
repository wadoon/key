package org.key_project.slicing;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Triple;
import org.key_project.slicing.graph.GraphNode;
import org.key_project.util.collection.ImmutableList;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

/**
 * Results of the dependency analysis algorithm.
 *
 * @see DependencyTracker#analyze()
 * @author Arne Keller
 */
public final class AnalysisResults {
    /**
     * Total amount of rule applications.
     */
    public final int totalSteps;
    /**
     * Amount of useful rule applications.
     */
    public final int usefulStepsNr;
    /**
     * Mapping of (rule display name)
     * to (total applications, useless applications, initial useless applications).
     */
    public final RuleStatistics ruleStatistics;
    /**
     * Set of useful rule applications.
     */
    public final Set<Node> usefulSteps;
    /**
     * Set of graph nodes required by useful rule applications.
     */
    public final Set<GraphNode> usefulNodes;
    private final Set<ImmutableList<String>> uselessBranches;

    public AnalysisResults(
            int totalSteps,
            int usefulStepsNr,
            RuleStatistics ruleStatistics,
            Set<Node> usefulSteps,
            Set<GraphNode> usefulNodes,
            Set<ImmutableList<String>> uselessBranches
    ) {
        this.totalSteps = totalSteps;
        this.usefulStepsNr = usefulStepsNr;
        this.ruleStatistics = ruleStatistics;
        this.usefulSteps = Collections.unmodifiableSet(usefulSteps);
        this.usefulNodes = Collections.unmodifiableSet(usefulNodes);
        this.uselessBranches = uselessBranches;
    }

    public boolean branchIsUseful(ImmutableList<String> branchLocation) {
        return uselessBranches.stream().noneMatch(branchLocation::hasPrefix);
    }

    @Override
    public String toString() {
        return "AnalysisResults{" +
                "totalSteps=" + totalSteps +
                ", usefulSteps=" + usefulStepsNr +
                '}';
    }
}
