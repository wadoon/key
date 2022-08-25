package org.key_project.slicing;

import de.uka.ilkd.key.proof.BranchLocation;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.slicing.graph.GraphNode;
import org.key_project.slicing.util.ExecutionTime;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Results of the dependency analysis algorithm.
 *
 * @see DependencyTracker#analyze(boolean, boolean)
 * @author Arne Keller
 */
public final class AnalysisResults {
    public final Proof proof;
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
    public final Set<BranchLocation> uselessBranches;
    public final Map<Node, List<Node>> branchStacks;

    public final boolean didDependencyAnalysis;
    public final boolean didDeduplicateRuleApps;
    public final ExecutionTime executionTime;

    public AnalysisResults(
            Proof proof,
            int totalSteps,
            RuleStatistics ruleStatistics,
            Set<Node> usefulSteps,
            Set<GraphNode> usefulNodes,
            Set<BranchLocation> uselessBranches,
            Map<Node, List<Node>> branchStacks,
            boolean didDependencyAnalysis,
            boolean didDeduplicateRuleApps,
            ExecutionTime executionTime
    ) {
        this.proof = proof;
        this.totalSteps = totalSteps;
        this.usefulStepsNr = usefulSteps.size();
        this.ruleStatistics = ruleStatistics;
        this.usefulSteps = Collections.unmodifiableSet(usefulSteps);
        this.usefulNodes = Collections.unmodifiableSet(usefulNodes);
        this.uselessBranches = Collections.unmodifiableSet(uselessBranches);
        this.branchStacks = branchStacks;
        this.didDependencyAnalysis = didDependencyAnalysis;
        this.didDeduplicateRuleApps = didDeduplicateRuleApps;
        this.executionTime = executionTime;
    }

    public boolean branchIsUseful(BranchLocation branchLocation) {
        return uselessBranches.stream().noneMatch(branchLocation::hasPrefix);
    }

    @Override
    public String toString() {
        return "AnalysisResults{" +
                "totalSteps=" + totalSteps +
                ", usefulSteps=" + usefulStepsNr +
                ", ...}";
    }
}
