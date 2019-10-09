package de.uka.ilkd.key.strategy.conflictbasedinst.statistics;

import java.io.File;

import de.uka.ilkd.key.proof.Proof;

public class CbiStatistics {

    //private static final Pattern PROOF_NAME_PATTERN = Pattern.compile("/([^/]*/[^/]*\\.key)");
    //private static final Pattern PROOF_PATH_PATTERN = Pattern.compile(regex)

    private static class InstanceHolder {
        private static final CbiStatistics INSTANCE = new CbiStatistics();
    }

    private static CbiStatistics instance() {
        return InstanceHolder.INSTANCE;
    }

    private ProofStatistics proof;
    private boolean enabled;

    private CbiStatistics() {
        proof = null;
        enabled = false;
    }

    public static void newProof(File keyFile) {
        String name = keyFile.getAbsolutePath();
        //Matcher matcher = PROOF_NAME_PATTERN.matcher(name);
        //instance().newProof(matcher.find() ? matcher.group(1) : name);
        int slix = name.lastIndexOf("examples/");

        instance().newProof(slix >= 0 ? name.substring(slix) : name);
    }

    private void newProof(String name) {
        this.proof = new ProofStatistics(name);
        this.enabled = true;
    }

    static boolean disabled() {
        return instance().enabled == false;
    }

    public static void startEmatching() {
        if(disabled()) return;
        instance().proof.startEmatching();
    }

    public static void finishEmatching(boolean success) {
        if(disabled()) return;
        instance().proof.finishEmatching(success);
    }

    public static void startCbi() {
        if(disabled()) return;
        instance().proof.startCbi();
    }

    public static void finishCbi(boolean success, boolean inducing) {
        if(disabled()) return;
        instance().proof.finishCbi(success, inducing);
    }

    public static void incEqualityInScope() {
        if(disabled()) return;
        instance().proof.incEqualityInScope();
    }

    public static void startCbiSubproof() {
        if(disabled()) return;
        instance().proof.startCbiSubproof();
    }

    public static void finishCbiSubproof() {
        if(disabled()) return;
        instance().proof.finishCbiSubproof();
    }

    public static void startNormalization() {
        if(disabled()) return;
        instance().proof.startNormalisation();
    }

    public static void finishNormalization() {
        if(disabled()) return;
        instance().proof.finishNormalisation();
    }

    public static void finishProof(Proof proof) {
        if(disabled()) return;
        instance().proof.finish(proof);
    }

    public static ProofStatistics getProofStatistics() {
        if(disabled()) return null;
        return instance().proof;
    }
}
