package de.uka.ilkd.key.strategy.conflictbasedinst.statistics;

import java.util.Iterator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;

public class ProofStatistics {

    private String name;

    // E-Matching
    private long ematchings;
    private long ematchingInstances;
    private long ematchingMillis;

    // CBI
    private long cbis;
    private long cbiInstances;
    private long cbiInducing;
    private long cbiEquality;
    private long cbiMillis;
    private long cbiSubproofMillis;

    // Normalisation
    private long normByRule;
    private long normInBG;
    private long normalisationMillis;

    // Total
    private long ruleApps;
    private long nodes;
    private long branches;
    private long overallMillis;
    private boolean closed;
    private long memoryKiloBytes;

    public ProofStatistics(String name) {
        this.name = name;
        ematchings = 0;
        ematchingInstances = 0;
        ematchingMillis = 0;
        cbis = 0;
        cbiInstances = 0;
        cbiInducing = 0;
        cbiEquality = 0;
        cbiMillis = 0;
        cbiSubproofMillis = 0;
        normByRule = 0;
        normInBG = 0;
        normalisationMillis = 0;
        ruleApps = 0;
        nodes = 0;
        branches = 0;
        overallMillis = 0;
        closed = false;
        memoryKiloBytes = 0;
    }

    private long ematchingTimestamp;

    public void startEmatching() {
        ematchings ++;
        ematchingTimestamp = System.currentTimeMillis();
    }

    public void finishEmatching(boolean success) {
        ematchingMillis += System.currentTimeMillis() - ematchingTimestamp;
        if(success) ematchingInstances++;
    }

    private long cbiTimestamp;

    public void startCbi() {
        cbis ++;
        cbiTimestamp = System.currentTimeMillis();
    }

    public void incEqualityInScope() {
        cbiEquality++;
    }

    public void finishCbi(boolean success, boolean inducing) {
        cbiMillis = cbiMillis + (System.currentTimeMillis() - cbiTimestamp);
        if(success) cbiInstances++;
        if(inducing) cbiInducing++;
    }

    private long cbiSubProofTimestamp;

    public void startCbiSubproof() {
        cbiSubProofTimestamp = System.currentTimeMillis();
    }

    public void finishCbiSubproof() {
        cbiSubproofMillis += System.currentTimeMillis() - cbiSubProofTimestamp;
    }

    private long normalisationTimestamp;

    public void startNormalisation() {
        normInBG++;
        normalisationTimestamp = System.currentTimeMillis();
    }

    public void finishNormalisation() {
        normalisationMillis += System.currentTimeMillis() - normalisationTimestamp;
    }

    private static final Pattern NORMALIZATION_RULES_PATTERN = Pattern.compile(
            "^nnf_.*|"
            + "^applyEq_(and|or)_gen.*|"
            + "^shift_parent_.*|"
            + "^commute_(and|or).*|"
            + "^cnf_rightDist|"
            + "^cnf_eqv|"
            + "^ifthenelse_to_.*|"
            + "^elim_(forall|exists).*|"
            + "^swapQuantifiers(All|Ex)|"
            + "^distr_(forall|exists)(And|Or).*|"
            + "^(all|ex)_pull_out.*|"
            + "^ifEquals(Null|TRUE|Integer)");

    public void finish(Proof proof) {
        Statistics stats = proof.getStatistics();

        this.closed = proof.closed();
        this.branches = stats.branches;
        Runtime.getRuntime().gc();
        this.memoryKiloBytes = (Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory()) / 1024;
        this.ruleApps = stats.totalRuleApps;
        this.overallMillis = stats.timeInMillis;
        Iterator<Node> it = proof.root().subtreeIterator();
        while(it.hasNext()) {
            Matcher matcher = NORMALIZATION_RULES_PATTERN.matcher(it.next().name());
            if(matcher.find()) normByRule++;
        }
    }

    public long getNormalisationMillis() {
        return normalisationMillis;
    }

    public void setNormalisationMillis(long normalisationMillis) {
        this.normalisationMillis = normalisationMillis;
    }

    public String getName() {
        return name;
    }

    public long getEmatchings() {
        return ematchings;
    }

    public long getEmatchingInstances() {
        return ematchingInstances;
    }

    public long getEmatchingMillis() {
        return ematchingMillis;
    }

    public long getCbis() {
        return cbis;
    }

    public long getCbiInstances() {
        return cbiInstances;
    }

    public long getCbiInducing() {
        return cbiInducing;
    }

    public long getCbiEquality() {
        return cbiEquality;
    }

    public long getCbiMillis() {
        return cbiMillis;
    }

    public long getCbiSubproofMillis() {
        return cbiSubproofMillis;
    }

    public long getNormByRule() {
        return normByRule;
    }

    public long getNormInBG() {
        return normInBG;
    }

    public long getRuleApps() {
        return ruleApps;
    }

    public long getNodes() {
        return nodes;
    }

    public long getBranches() {
        return branches;
    }

    public long getOverallMillis() {
        return overallMillis;
    }

    public boolean isClosed() {
        return closed;
    }

    public long getMemoryKiloBytes() {
        return memoryKiloBytes;
    }


}
