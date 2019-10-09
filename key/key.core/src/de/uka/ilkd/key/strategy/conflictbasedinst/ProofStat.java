package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.LinkedList;
import java.util.List;

public class ProofStat {

    private String name;
    private long normRuleApps;
    private List<FeatureStat> instStats;

    public ProofStat(String name) {
        this.name = name;
        this.normRuleApps = 0;
        instStats = new LinkedList<FeatureStat>();
    }


    public void addStat(FeatureStat stat) {
        instStats.add(stat);
    }

    public String getName() {
        return name;
    }

    public List<FeatureStat> getStats() {
        return instStats;
    }


    public void incNormRuleApps() {
        normRuleApps++;
    }


    public Object getNormRuleApps() {
        return normRuleApps;
    }

}
