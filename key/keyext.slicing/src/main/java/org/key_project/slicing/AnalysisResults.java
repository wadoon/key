package org.key_project.slicing;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Triple;
import org.key_project.slicing.graph.TrackedFormula;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

public class AnalysisResults {
    public final int totalSteps;
    public final int usefulStepsNr;
    /**
     * displayName of rule -> (total applications, useless applications, initial useless applications)
     */
    public final Map<String, Triple<Integer, Integer, Integer>> ruleStatistics;
    public final Set<Node> usefulSteps;
    public final Set<TrackedFormula> usefulFormulas;

    public AnalysisResults(int totalSteps, int usefulStepsNr, Map<String, Triple<Integer, Integer, Integer>> ruleStatistics, Set<Node> usefulSteps, Set<TrackedFormula> usefulFormulas) {
        this.totalSteps = totalSteps;
        this.usefulStepsNr = usefulStepsNr;
        this.ruleStatistics = Collections.unmodifiableMap(ruleStatistics);
        this.usefulSteps = Collections.unmodifiableSet(usefulSteps);
        this.usefulFormulas = Collections.unmodifiableSet(usefulFormulas);
    }

    @Override
    public String toString() {
        return "AnalysisResults{" +
                "totalSteps=" + totalSteps +
                ", usefulSteps=" + usefulStepsNr +
                '}';
    }
}
