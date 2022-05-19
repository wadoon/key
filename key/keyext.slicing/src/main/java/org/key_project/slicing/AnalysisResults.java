package org.key_project.slicing;

import de.uka.ilkd.key.util.Triple;

import java.util.Map;

public class AnalysisResults {
    public int totalSteps;
    public int usefulSteps;
    /**
     * displayName of rule -> (total applications, useless applications, initial useless applications)
     */
    public Map<String, Triple<Integer, Integer, Integer>> ruleStatistics;

    public AnalysisResults(int totalSteps, int usefulSteps, Map<String, Triple<Integer, Integer, Integer>> ruleStatistics) {
        this.totalSteps = totalSteps;
        this.usefulSteps = usefulSteps;
        this.ruleStatistics = ruleStatistics;
    }

    @Override
    public String toString() {
        return "AnalysisResults{" +
                "totalSteps=" + totalSteps +
                ", usefulSteps=" + usefulSteps +
                '}';
    }
}
