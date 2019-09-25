package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.LinkedList;
import java.util.List;

public class ProofStat {

    private String name;
    private boolean statistics;
    private List<FeatureStat> instStats;

    public ProofStat(String name) {
        this.name = name;
        statistics = true;
        instStats = new LinkedList<FeatureStat>();
    }

    public void setStatistics(boolean statistics) {
        this.statistics = statistics;
    }

    public void addStat(FeatureStat stat) {
        instStats.add(stat);
    }

    public String getName() {
        return name;
    }

    public boolean hasStatistics() {
        return statistics;
    }

    public List<FeatureStat> getStats() {
        return instStats;
    }

}
