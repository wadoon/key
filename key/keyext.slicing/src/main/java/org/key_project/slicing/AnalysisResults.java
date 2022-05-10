package org.key_project.slicing;

import java.util.Objects;

public class AnalysisResults {
    public int totalSteps;
    public int usefulSteps;

    public AnalysisResults(int totalSteps, int usefulSteps) {
        this.totalSteps = totalSteps;
        this.usefulSteps = usefulSteps;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        AnalysisResults that = (AnalysisResults) o;
        return totalSteps == that.totalSteps && usefulSteps == that.usefulSteps;
    }

    @Override
    public int hashCode() {
        return Objects.hash(totalSteps, usefulSteps);
    }

    @Override
    public String toString() {
        return "AnalysisResults{" +
                "totalSteps=" + totalSteps +
                ", usefulSteps=" + usefulSteps +
                '}';
    }
}
